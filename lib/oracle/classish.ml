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
  [@@deriving eq, compare, sexp, show, variants]
end

module Entry = struct
  type t =
    { ty_params : Ty_param_def.t list
    (** The type parameters declared in the class along with there declared bounds *)
    ; supers : Ty.t list Name.Ctor.Map.t
    ; span : Span.t
    ; kind : Classish_def.Kind.t Located.t
    (** Any superclass the class extends and the list any interfaces it implements. The args in each [Ty.Ctor.t]
        must either be concreate types or be bound *)
    }
  [@@deriving show]

  let of_classish_def
    Classish_def.{ ty_params; extends; implements; kind; _ }
    span
    =
    let f (supers, spans, errs) Located.{ elem = Ty.Ctor.{ name; args }; span } =
      match Map.add supers ~key:name ~data:args with
      | `Ok supers -> supers, Map.add_exn spans ~key:name ~data:span, errs
      | `Duplicate ->
        let span_first = Map.find_exn spans name in
        let err =
          Err.multiple_instantiation ~span_first ~span_next:span ~ctor_name:name
        in
        supers, spans, err :: errs
    in
    let init =
      Option.value_map
        extends
        ~f:(fun Located.{ elem = Ty.Ctor.{ name; args }; span } ->
          ( Name.Ctor.Map.singleton name args
          , Name.Ctor.Map.singleton name span
          , [] ))
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
  Option.map ~f:(List.map ~f:(fun Ty_param_def.{ variance; _ } -> variance))
  @@ params_opt t ctor
;;

let param_bounds_opt t ~ctor =
  let Ty.Ctor.{ name; args } = ctor in
  match params_opt t name with
  | Some params ->
    Some
      (Map.map ~f:Ty.Param_bounds.(meet_many ~prov:Reporting.Prov.empty)
       @@ Name.Ty_param.Map.of_alist_multi
       @@ List.filter_opt
       @@ List.map2_exn
            args
            params
            ~f:(fun arg Ty_param_def.{ param_bounds; _ } ->
              match arg.node with
              | Ty.Node.Generic g -> Some (g, param_bounds)
              | _ -> None))
  | None -> None
;;

type instantiation =
  | Not_a_subclass
  | Direct of Ty.t list
  | Transitive of Ty.t list

(** Find the instantiation of constructor type [of_] at the constructor name [at].
    When [of_] is a transitive subclass of [at] this will return the types at
    which the [of_] is instantiated when viewed at the superclass [at] *)
let rec up (t : t) ~of_ ~at =
  let Ty.Ctor.{ name = of_id; args = of_args } = of_ in
  (* First, is do we have an entry for the subclass *)
  match Map.find t of_id with
  (* The oracle has no information about the [of_] class type *)
  | None -> Not_a_subclass
  (* The class exists but we're asking for an instantiation at itself so just return the args *)
  | Some _ when Name.Ctor.equal of_id at -> Direct of_args
  (* Yes; check is the superclass is in the list of declared supers *)
  | Some Entry.{ supers; ty_params; _ } ->
    (* 1) Build a substitution from the declared type params back to the actual type arguments of the subclass.
       We use [List.map2_exn] here since we assume the class type is well-formed which guarantees the list of arguments
       and list of parameters have the same length.
    *)
    let subst =
      Name.Ty_param.Map.of_alist_exn
      @@ List.map2_exn ty_params of_args ~f:(fun { name; _ } arg ->
        name.elem, arg)
    in
    (* Any class can be viewed at its superclass *)
    (match Map.find supers at with
     (* The class type directly declares [at] as an ancestor; the args of [at] must either be a generic bound in the
        subclass declaration _or_ a concrete type. Collect the generic type arguments and lookup the declared bounds
        on [of_] *)
     | Some args ->
       Direct
         (List.map args ~f:(Ty.apply_subst ~subst ~combine_prov:(fun _ p -> p)))
     (* No; search the transitive supertypes *)
     | None ->
       Option.value ~default:Not_a_subclass
       @@ List.hd
       @@ List.filter_map ~f:(fun (name, args) ->
         (* Instantiate the superclass at the provided arguments and make the recursive call *)
         let args =
           List.map args ~f:(Ty.apply_subst ~subst ~combine_prov:(fun _ p -> p))
         in
         let of_ = Ty.Ctor.{ name; args } in
         match up t ~of_ ~at with
         | Direct args | Transitive args -> Some (Transitive args)
         | Not_a_subclass -> None)
       @@ Map.to_alist supers)
;;

let find (t : t) id =
  Option.map ~f:(fun Entry.{ ty_params; supers; _ } -> ty_params, supers)
  @@ Map.find t id
;;

let empty = Name.Ctor.Map.empty

let add t (Classish_def.{ name; _ } as classish_def) span
  : (t * Err.t list, Err.t * Err.t list) result
  =
  let data, multi_inst_errs = Entry.of_classish_def classish_def span in
  let key = name.elem in
  match Map.add t ~key ~data with
  | `Ok t -> Ok (t, multi_inst_errs)
  | `Duplicate ->
    let err = Err.already_declared ~ctor_name:name.elem ~span in
    Error (err, multi_inst_errs)
;;
