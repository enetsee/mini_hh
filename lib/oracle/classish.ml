open Core
open Reporting
open Lang

module Err = struct
  type t =
    | Multiple_instantiation of
        { span_first : Span.t
        ; span_next : Span.t
        ; ctor_name : Name.Ctor.t
        }
    | Already_declared of
        { ctor_name : Name.Ctor.t
        ; span : Span.t
        }
  [@@deriving eq, compare, sexp, variants]
end

module Entry = struct
  type t =
    { ty_params : Ty_param_def.t list (** The type parameters declared in the class along with there declared bounds *)
    ; supers : Ty.t list Name.Ctor.Map.t
    ; span : Span.t
    ; kind : Classish_kind.t Located.t
    (** Any superclass the class extends and the list any interfaces it implements. The args in each [Ty.Ctor.t]
        must either be concreate types or be bound *)
    }
  [@@deriving show]

  let of_classish_def Classish_def.{ ty_params; extends; implements; kind; _ } span =
    (* TODO(mjt) this should survive errors *)
    let f (supers, spans, errs) Located.{ elem = Ty.Ctor.{ name; args }; span } =
      match Map.add supers ~key:name ~data:args with
      | `Ok supers -> supers, Map.add_exn spans ~key:name ~data:span, errs
      | `Duplicate ->
        let span_first = Map.find_exn spans name in
        let err = Err.multiple_instantiation ~span_first ~span_next:span ~ctor_name:name in
        supers, spans, err :: errs
    in
    let init =
      Option.value_map
        extends
        ~f:(fun Located.{ elem = Ty.Ctor.{ name; args }; span } ->
          Name.Ctor.Map.singleton name args, Name.Ctor.Map.singleton name span, [])
        ~default:(Name.Ctor.Map.empty, Name.Ctor.Map.empty, [])
    in
    let supers, _, errs = List.fold_left implements ~f ~init in
    { supers; ty_params; span; kind }, errs
  ;;
end

type t = Entry.t Name.Ctor.Map.t [@@deriving show]

let collect_generics =
  let ops = Ty.Ops.collect_generics () in
  fun ty -> Ty.bottom_up ~ops ~init:Name.Ty_param.Set.empty ty
;;

let entry (t : t) ctor = Map.find t ctor

let params_opt (t : t) ctor =
  match Map.find t ctor with
  | Some Entry.{ ty_params; _ } -> Some ty_params
  | _ -> None
;;

let supers_opt (t : t) ctor =
  match Map.find t ctor with
  | Some Entry.{ supers; _ } -> Some supers
  | _ -> None
;;

let param_variances_opt t ctor =
  Option.map ~f:(List.map ~f:(fun Ty_param_def.{ variance; _ } -> variance)) @@ params_opt t ctor
;;

let param_bounds_opt t ~ctor =
  let Ty.Ctor.{ name; args } = ctor in
  match params_opt t name with
  | Some params ->
    Some
      (Map.map ~f:Ty.Param_bounds.(meet_many ~prov:Reporting.Prov.empty)
       @@ Name.Ty_param.Map.of_alist_multi
       @@ List.filter_opt
       @@ List.map2_exn args params ~f:(fun arg Ty_param_def.{ bounds; _ } ->
         match arg.node with
         | Ty.Node.Generic g -> Some (g, bounds)
         | _ -> None))
  | None -> None
;;

let rec up (t : t) ~of_ ~at =
  let Ty.Ctor.{ name = of_id; args = of_args } = of_ in
  (* First, is do we have an entry for the subclass *)
  match Map.find t of_id with
  (* The oracle has no information about the [of_] class type *)
  | None -> None
  (* The class exists but we're asking for an instantiation at itself so just return the args *)
  | Some _ when Name.Ctor.equal of_id at -> Some of_args
  (* Yes; check is the superclass is in the list of declared supers *)
  | Some Entry.{ supers; ty_params; _ } ->
    (* 1) Build a substitution from the declared type params back to the actual type arguments of the subclass.
       We use [List.map2_exn] here since we assume the class type is well-formed which guarantees the list of arguments
       and list of parameters have the same length.
    *)
    let subst =
      Name.Ty_param.Map.of_alist_exn @@ List.map2_exn ty_params of_args ~f:(fun { name; _ } arg -> name.elem, arg)
    in
    (* Any class can be viewed at its superclass *)
    (match Map.find supers at with
     (* The class type directly declares [at] as an ancestor; the args of [at] must either be a generic bound in the
        subclass declaration _or_ a concrete type. Collect the generic type arguments and lookup the declared bounds
        on [of_] *)
     | Some args -> Some (List.map args ~f:(Ty.apply_subst ~subst ~combine_prov:(fun _ p -> p)))
     (* No; search the transitive supertypes *)
     | None ->
       List.hd
       @@ List.filter_map ~f:(fun (name, args) ->
         (* Instantiate the superclass at the provided arguments and make the recursive call *)
         let args = List.map args ~f:(Ty.apply_subst ~subst ~combine_prov:(fun _ p -> p)) in
         let of_ = Ty.Ctor.{ name; args } in
         up t ~of_ ~at)
       @@ Map.to_alist supers)
;;

(** TODO(mjt) pretty sure this isn't right and isn't generally possible - this should be moved to refinement
    and the case where we have
    I<+T1,-T2>
    C<T> implements I<T,T>
    then
    I<a,b> `down` C
    should be an error *)
let down t ~of_ ~at =
  let Ty.Ctor.{ name = of_id; args = of_args } = of_ in
  (* Find [up ~of_:at ~at:of_] with  [at] applied to its declared generics *)
  match Map.find t at with
  | None -> None
  | Some _ when Name.Ctor.equal of_id at -> Some of_args
  | Some Entry.{ ty_params; _ } ->
    let at_args =
      List.map ty_params ~f:(fun { name = Located.{ elem; span }; _ } -> Ty.generic Prov.(witness span) elem)
    in
    (match up t ~of_:Ty.Ctor.{ name = at; args = at_args } ~at:of_id with
     | None -> None
     | Some args_up ->
       (* [args_up] now contains generics at the positions we want to extract from [of_args]
          so we zip them together and build a map. We can end up with multiple different types:

          class B<T> extends C<T,T>

          then say we want to go down C<X,Y> -> B we have T |-> [X,Y] so what type should we use?
       *)
       let subst =
         (* TODO(mjt): shouldn't this be using variance and using least upper bound for contravariant params *)
         Name.Ty_param.Map.map ~f:Ty.(inter ~prov:Reporting.Prov.empty)
         @@ Name.Ty_param.Map.of_alist_multi
         @@ List.filter_opt
         @@ List.map2_exn args_up of_args ~f:(fun arg_up of_arg ->
           match arg_up.node with
           | Ty.Node.Generic g -> Some (g, of_arg)
           | _ -> None)
       in
       Some (List.map ty_params ~f:(fun { name; _ } -> Map.find_exn subst name.elem)))
;;

let find (t : t) id = Option.map ~f:(fun Entry.{ ty_params; supers; _ } -> ty_params, supers) @@ Map.find t id
let empty = Name.Ctor.Map.empty

let add t (Classish_def.{ name; _ } as classish_def) span : (t * Err.t list, Err.t * Err.t list) result =
  let data, multi_inst_errs = Entry.of_classish_def classish_def span in
  let key = name.elem in
  match Map.add t ~key ~data with
  | `Ok t -> Ok (t, multi_inst_errs)
  | `Duplicate ->
    let err = Err.already_declared ~ctor_name:name.elem ~span in
    Error (err, multi_inst_errs)
;;
