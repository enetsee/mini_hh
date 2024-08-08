open Core
open Common

module Entry = struct
  type t =
    { ty_params : (Ty.Generic.t * Variance.t * Ty.Param_bounds.t) list
    (** The type parameters declared in the class along with there declared bounds *)
    ; supers : Ty.t list Identifier.Ctor.Map.t
    (** Any superclass the class extends and the list any interfaces it implements. The args in each [Ty.Ctor.t]
        must either be concreate types or be bound *)
    }
  [@@deriving show]
end

type t = Entry.t Identifier.Ctor.Map.t [@@deriving show]

let collect_generics =
  let ops = Ty.Ops.collect_generics () in
  fun ty -> Ty.bottom_up ~ops ~init:Ty.Generic.Set.empty ty
;;

let up (t : t) ~of_ ~at =
  let Ty.Ctor.{ ctor = of_id; args = of_args } = of_ in
  (* and Ty.Ctor.{ ctor = at_id; _ } = at in *)
  (* First, is do we have an entry for the subclass *)
  match Map.find t of_id with
  (* Nope; there is no instantiation of the subclass at the provided ancestor *)
  | None -> None
  (* Yes; Now check is the superclass is in the list of declared supers *)
  | Some Entry.{ supers; ty_params } ->
    (* Build a map from the declared type params back to the actual type arguments of the subclass *)
    let args_map =
      Ty.Generic.Map.of_alist_exn @@ List.map2_exn ty_params of_args ~f:(fun (src, _, _) dest -> src, dest)
    in
    (match Map.find supers at with
     (* No; TODO(mjt) search the transitive supertypes *)
     | None -> None
     (* Yes; each declared type must either be a generic bound in the subclass declaration _or_ a concrete type*)
     | Some args ->
       let generics =
         Ty.Generic.Map.of_alist_exn
         @@ List.filter_map ~f:(fun generic ->
           match List.find ty_params ~f:(fun (g, _, _) -> Ty.Generic.equal generic g) with
           | None -> None
           | Some (_, _, bounds) ->
             (* We only refine bounds if the generic occurs in of_ *)
             (match Map.find args_map generic with
              | Some (Ty.Generic generic) -> Some (generic, bounds)
              | _ -> None))
         @@ Set.elements
         @@ Ty.Generic.Set.union_list
         @@ List.map args ~f:collect_generics
       in
       Some (List.map args ~f:(Ty.apply_subst ~subst:args_map), generics))
;;

let find (t : t) id = Option.map ~f:(fun Entry.{ ty_params; supers } -> ty_params, supers) @@ Map.find t id

module Example = struct
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
    Identifier.Ctor.Map.of_alist_exn
      [ (* class A {}  *)
        (Identifier.Ctor.Ctor "A", Entry.{ ty_params = []; supers = Identifier.Ctor.Map.empty })
        (* class B extends A {} *)
      ; ( Identifier.Ctor.Ctor "B"
        , Entry.{ ty_params = []; supers = Identifier.Ctor.Map.of_alist_exn [ Identifier.Ctor.Ctor "A", [] ] } )
        (* class C extends B {} *)
      ; ( Identifier.Ctor.Ctor "C"
        , Entry.{ ty_params = []; supers = Identifier.Ctor.Map.of_alist_exn [ Identifier.Ctor.Ctor "B", [] ] } )
        (* interface I<T> {} *)
      ; ( Identifier.Ctor.Ctor "I"
        , Entry.
            { ty_params = [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
            ; supers = Identifier.Ctor.Map.empty
            } )
        (* interface J<T> {} *)
      ; ( Identifier.Ctor.Ctor "J"
        , Entry.
            { ty_params = [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
            ; supers = Identifier.Ctor.Map.empty
            } )
        (* interface K<T1,T2> {} *)
      ; ( Identifier.Ctor.Ctor "K"
        , Entry.
            { ty_params =
                [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
            ; supers = Identifier.Ctor.Map.empty
            } )
        (* interface L<T1,T2> {} *)
      ; ( Identifier.Ctor.Ctor "L"
        , Entry.
            { ty_params =
                [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
            ; supers = Identifier.Ctor.Map.empty
            } )
        (* interface M<T> {} *)
      ; ( Identifier.Ctor.Ctor "M"
        , Entry.
            { ty_params = [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
            ; supers = Identifier.Ctor.Map.empty
            } )
        (* class D<T super A> implements M<T> {} *)
      ; ( Identifier.Ctor.Ctor "D"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = Some (Ty.ctor (Identifier.Ctor.Ctor "A") []); upper_bound = None }
                  )
                ]
            ; supers =
                Identifier.Ctor.Map.of_alist_exn
                  [ Identifier.Ctor.Ctor "M", [ Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ]
            } )
        (* class E<T as B> implements I<T> {} *)
      ; ( Identifier.Ctor.Ctor "E"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = None; upper_bound = Some (Ty.ctor (Identifier.Ctor.Ctor "B") []) }
                  )
                ]
            ; supers =
                Identifier.Ctor.Map.of_alist_exn
                  [ Identifier.Ctor.Ctor "I", [ Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ]
            } )
        (* class F implements  J<bool>  {} *)
      ; ( Identifier.Ctor.Ctor "F"
        , Entry.{ ty_params = []; supers = Identifier.Ctor.Map.of_alist_exn [ Identifier.Ctor.Ctor "J", [ Ty.bool ] ] }
        )
        (* class G<T as C> implements K<T,int> {} *)
      ; ( Identifier.Ctor.Ctor "G"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = None; upper_bound = Some (Ty.ctor (Identifier.Ctor.Ctor "C") []) }
                  )
                ]
            ; supers =
                Identifier.Ctor.Map.of_alist_exn
                  [ Identifier.Ctor.Ctor "K", [ Ty.generic @@ Identifier.Ty_param.Ty_param "T"; Ty.bool ] ]
            } )
        (* class H<T1 as B, T2 as C> implements L<T2, T1> {} *)
      ; ( Identifier.Ctor.Ctor "H"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = None; upper_bound = Some (Ty.ctor (Identifier.Ctor.Ctor "B") []) }
                  )
                ; ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = None; upper_bound = Some (Ty.ctor (Identifier.Ctor.Ctor "C") []) }
                  )
                ]
            ; supers =
                Identifier.Ctor.Map.of_alist_exn
                  [ ( Identifier.Ctor.Ctor "L"
                    , [ Ty.generic @@ Identifier.Ty_param.Ty_param "T1"
                      ; Ty.generic @@ Identifier.Ty_param.Ty_param "T2"
                      ] )
                  ]
            } )
        (* class AA implements I<bool> , J<bool> *)
      ; ( Identifier.Ctor.Ctor "AA"
        , Entry.
            { ty_params = []
            ; supers =
                Identifier.Ctor.Map.of_alist_exn
                  [ Identifier.Ctor.Ctor "I", [ Ty.bool ]; Identifier.Ctor.Ctor "J", [ Ty.bool ] ]
            } )
        (* class BB implements I<bool> , J<int> *)
      ; ( Identifier.Ctor.Ctor "BB"
        , Entry.
            { ty_params = []
            ; supers =
                Identifier.Ctor.Map.of_alist_exn
                  [ Identifier.Ctor.Ctor "I", [ Ty.bool ]; Identifier.Ctor.Ctor "J", [ Ty.int ] ]
            } )
        (* class CC<T super int as (int | string)> implements I<int>, J<T> {} *)
      ; ( Identifier.Ctor.Ctor "CC"
        , Entry.
            { ty_params =
                [ ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.{ lower_bound = Some Ty.int; upper_bound = Some Ty.(union [ int; string ]) } )
                ]
            ; supers =
                Identifier.Ctor.Map.of_alist_exn
                  [ Identifier.Ctor.Ctor "I", [ Ty.int ]
                  ; Identifier.Ctor.Ctor "J", [ Ty.generic (Identifier.Ty_param.Ty_param "T") ]
                  ]
            } )
      ]
  ;;
end
