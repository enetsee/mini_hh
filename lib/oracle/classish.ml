open Core
open Common

module Entry = struct
  type t =
    { ty_params : (Name.Ty_param.t * Variance.t * Ty.Param_bounds.t * Reporting.Loc.t) list
    (** The type parameters declared in the class along with there declared bounds *)
    ; supers : Ty.t list Name.Ctor.Map.t
    (** Any superclass the class extends and the list any interfaces it implements. The args in each [Ty.Ctor.t]
        must either be concreate types or be bound *)
    }
  [@@deriving show]
end

type t = Entry.t Name.Ctor.Map.t [@@deriving show]

let collect_generics =
  let ops = Ty.Ops.collect_generics () in
  fun ty -> Ty.bottom_up ~ops ~init:Name.Ty_param.Set.empty ty
;;

(* let param_bounds_opt generic ~ty_params ~param_arg_map =
   match List.find ty_params ~f:(fun (g, _, _) -> Ty.Generic.equal generic g) with
   | None -> None
   | Some (_, _, bounds) ->
   (* We only refine bounds if the generic occurs in of_ *)
   (match Map.find param_arg_map generic with
   | Some (Ty.Generic generic) -> Some (generic, bounds)
   | _ -> None)
   ;; *)

(* let intersect ups ~prov =
   let rec aux ~k = function
   | [] -> None
   | [ (tys, bounds) ] -> k (List.map ~f:List.singleton tys, bounds)
   | (tys, bounds) :: rest ->
   aux rest ~k:(fun (tys_rest, bounds_rest) ->
   let tys = List.map2_exn tys tys_rest ~f:List.cons in
   let bounds = Envir.Ty_param.meet bounds bounds_rest in
   k (tys, bounds))
   in
   match ups with
   | [] -> None
   | _ -> aux ups ~k:(fun (tys, bounds) -> Some (List.map ~f:Ty.inter tys, bounds))
   ;; *)

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

let param_variances_opt t ctor = Option.map ~f:(List.map ~f:(fun (_, variance, _, _) -> variance)) @@ params_opt t ctor

let param_bounds_opt t ~ctor =
  let Ty.Ctor.{ name; args } = ctor in
  match params_opt t name with
  | Some params ->
    Some
      (Map.map ~f:Ty.Param_bounds.(meet_many ~prov:Reporting.Prov.empty)
       @@ Name.Ty_param.Map.of_alist_multi
       @@ List.filter_opt
       @@ List.map2_exn args params ~f:(fun arg (_, _, bounds, _) ->
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
  | Some Entry.{ supers; ty_params } ->
    (* 1) Build a substitution from the declared type params back to the actual type arguments of the subclass.
       We use [List.map2_exn] here since we assume the class type is well-formed which guarantees the list of arguments
       and list of parameters have the same length.
    *)
    let subst =
      Name.Ty_param.Map.of_alist_exn @@ List.map2_exn ty_params of_args ~f:(fun (param, _, _, _) arg -> param, arg)
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

let down t ~of_ ~at =
  let Ty.Ctor.{ name = of_id; args = of_args } = of_ in
  (* Find [up ~of_:at ~at:of_] with  [at] applied to its declared generics *)
  match Map.find t at with
  | None -> None
  | Some _ when Name.Ctor.equal of_id at -> Some of_args
  | Some Entry.{ ty_params; _ } ->
    let at_args = List.map ty_params ~f:(fun (g, _, _, loc) -> Ty.generic Reporting.Prov.(witness loc) g) in
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
       Some (List.map ty_params ~f:(fun (g, _, _, _) -> Map.find_exn subst g)))
;;

let find (t : t) id = Option.map ~f:(fun Entry.{ ty_params; supers } -> ty_params, supers) @@ Map.find t id
let empty = Name.Ctor.Map.empty

let add_exn (t : t) ~id ~ty_params ~supers : t =
  Map.add_exn t ~key:id ~data:Entry.{ ty_params; supers = Name.Ctor.Map.of_alist_exn supers }
;;

let add_all_exn (t : t) ls : t =
  List.fold_left ls ~init:t ~f:(fun t (id, ty_params, supers) -> add_exn t ~id ~ty_params ~supers)
;;

(* module Example = struct
  (* class A {} 
     class B extends A {}
     class C extends B {}
     interface I<T> {}
     interface J<T> {}
     interface K<T1,T2> {} 
     interface L<T1,T2> {}
     interface M<T> {}
     class D<T super A> implements M<T> {}
     class E<T as B> implements I<T> {}
     class F implements J<bool> {}
     class G<T as C> implements K<T,int> {}
     class H<T1 as B, T2 as C> implements L<T2, T1> {}

     class AA implements I<bool> , J<bool>
     class BB implements I<bool> , J<int>
  *)
  let data =
    Name.Ctor.Map.of_alist_exn
      [ (* class A {}  *)
        (Name.Ctor.Ctor "A", Entry.{ ty_params = []; supers = Name.Ctor.Map.empty }) (* class B extends A {} *)
      ; (Name.Ctor.Ctor "B", Entry.{ ty_params = []; supers = Name.Ctor.Map.of_alist_exn [ Name.Ctor.Ctor "A", [] ] })
        (* class C extends B {} *)
      ; (Name.Ctor.Ctor "C", Entry.{ ty_params = []; supers = Name.Ctor.Map.of_alist_exn [ Name.Ctor.Ctor "B", [] ] })
        (* interface I<T> {} *)
      ; ( Name.Ctor.Ctor "I"
        , Entry.
            { ty_params = [ Ty.Generic.Generic (Name.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
            ; supers = Name.Ctor.Map.empty
            } )
        (* interface J<T> {} *)
      ; ( Name.Ctor.Ctor "J"
        , Entry.
            { ty_params = [ Ty.Generic.Generic (Name.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
            ; supers = Name.Ctor.Map.empty
            } )
        (* interface K<T1,T2> {} *)
      ; ( Name.Ctor.Ctor "K"
        , Entry.
            { ty_params =
                [ Ty.Generic.Generic (Name.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Name.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
            ; supers = Name.Ctor.Map.empty
            } )
        (* interface L<T1,T2> {} *)
      ; ( Name.Ctor.Ctor "L"
        , Entry.
            { ty_params =
                [ Ty.Generic.Generic (Name.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Name.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
            ; supers = Name.Ctor.Map.empty
            } )
        (* interface M<T> {} *)
      ; ( Name.Ctor.Ctor "M"
        , Entry.
            { ty_params = [ Ty.Generic.Generic (Name.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
            ; supers = Name.Ctor.Map.empty
            } )
        (* class D<T super A> implements M<T> {} *)
      ; ( Name.Ctor.Ctor "D"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Name.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = Some (Ty.ctor (Name.Ctor.Ctor "A") []); upper_bound = None } )
                ]
            ; supers = Name.Ctor.Map.of_alist_exn [ Name.Ctor.Ctor "M", [ Ty.generic @@ Name.Ty_param.Ty_param "T" ] ]
            } )
        (* class E<T as B> implements I<T> {} *)
      ; ( Name.Ctor.Ctor "E"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Name.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = None; upper_bound = Some (Ty.ctor (Name.Ctor.Ctor "B") []) } )
                ]
            ; supers = Name.Ctor.Map.of_alist_exn [ Name.Ctor.Ctor "I", [ Ty.generic @@ Name.Ty_param.Ty_param "T" ] ]
            } )
        (* class F implements  J<bool>  {} *)
      ; ( Name.Ctor.Ctor "F"
        , Entry.{ ty_params = []; supers = Name.Ctor.Map.of_alist_exn [ Name.Ctor.Ctor "J", [ Ty.bool ] ] } )
        (* class G<T as C> implements K<T,int> {} *)
      ; ( Name.Ctor.Ctor "G"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Name.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = None; upper_bound = Some (Ty.ctor (Name.Ctor.Ctor "C") []) } )
                ]
            ; supers =
                Name.Ctor.Map.of_alist_exn [ Name.Ctor.Ctor "K", [ Ty.generic @@ Name.Ty_param.Ty_param "T"; Ty.bool ] ]
            } )
        (* class H<T1 as B, T2 as C> implements L<T2, T1> {} *)
      ; ( Name.Ctor.Ctor "H"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Name.Ty_param.Ty_param "T1")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = None; upper_bound = Some (Ty.ctor (Name.Ctor.Ctor "B") []) } )
                ; ( Ty.Generic.Generic (Name.Ty_param.Ty_param "T2")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = None; upper_bound = Some (Ty.ctor (Name.Ctor.Ctor "C") []) } )
                ]
            ; supers =
                Name.Ctor.Map.of_alist_exn
                  [ ( Name.Ctor.Ctor "L"
                    , [ Ty.generic @@ Name.Ty_param.Ty_param "T1"; Ty.generic @@ Name.Ty_param.Ty_param "T2" ] )
                  ]
            } )
        (* class AA implements I<bool> , J<bool> *)
      ; ( Name.Ctor.Ctor "AA"
        , Entry.
            { ty_params = []
            ; supers = Name.Ctor.Map.of_alist_exn [ Name.Ctor.Ctor "I", [ Ty.bool ]; Name.Ctor.Ctor "J", [ Ty.bool ] ]
            } )
        (* class BB implements I<bool> , J<int> *)
      ; ( Name.Ctor.Ctor "BB"
        , Entry.
            { ty_params = []
            ; supers = Name.Ctor.Map.of_alist_exn [ Name.Ctor.Ctor "I", [ Ty.bool ]; Name.Ctor.Ctor "J", [ Ty.int ] ]
            } )
        (* class CC<T super int as (int | string)> implements I<int>, J<T> {} *)
      ; ( Name.Ctor.Ctor "CC"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Name.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = Some Ty.int; upper_bound = Some Ty.(union [ int; string ]) } )
                ]
            ; supers =
                Name.Ctor.Map.of_alist_exn
                  [ Name.Ctor.Ctor "I", [ Ty.int ]; Name.Ctor.Ctor "J", [ Ty.generic (Name.Ty_param.Ty_param "T") ] ]
            } )
      ]
  ;;
end *)
