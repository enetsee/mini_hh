open Core
module Ctxt = Ctxt

let unify ~is_ ~scrut bounds =
  match is_, scrut with
  (* We have an equal generic in the same positions - nothing to do *)
  | Ty.Generic ty_param_is, Ty.Generic ty_param_scrut when Ty.Generic.equal ty_param_is ty_param_scrut -> bounds
  (* We have different genrics in the same position - this can only happen if
     the refining type is existential. We need to:
     - find the intersection of the bounds on the existential quantifier and
       those of the type from the scrutinee
     - solve the existential quantifier by modifyinf the bounds so that it is
       equal to type parameter scrutinee
  *)
  | Ty.Generic ty_param_is, Ty.Generic ty_param_scrut ->
    let bounds_is = Map.find_exn bounds ty_param_is in
    (* Refine the outer parameter bounds
       TODO(mjt)I don't think they can be already bound in the refinement? *)
    let bounds =
      Map.update bounds ty_param_scrut ~f:(function
        | None -> bounds_is
        | Some bounds_scrut -> Ty.Param_bounds.meet bounds_is bounds_scrut)
    in
    let bound_scrut = Ty.Param_bounds.eq scrut in
    (* Set the inner bounds equal to the outer bound *)
    Map.update bounds ty_param_is ~f:(function
      | None -> bound_scrut
      | Some _ -> bound_scrut)
    (* The refinement gave us a concrete type so update the bounds of the generic
       in scrutinee position
    *)
  | _, Ty.Generic ty_param_scrut ->
    let bounds_is = Ty.Param_bounds.eq is_ in
    Map.update bounds ty_param_scrut ~f:(function
      | None -> bounds_is
      | Some bounds_scrut -> Ty.Param_bounds.meet bounds_is bounds_scrut)
  (* We have a generic from the refining type but some other type in scrutinee
     position. Update the bounds on the existential to be equal to the
     scrutinee type
     TODO(mjt) which example exercises this? *)
  | Ty.Generic ty_param_is, _ ->
    let bound_scrut = Ty.Param_bounds.eq scrut in
    Map.update bounds ty_param_is ~f:(function
      | None -> bound_scrut
      | Some bound_is -> Ty.Param_bounds.meet bound_scrut bound_is)
  (* Otherwise they are both concrete and we leave it for subtyping to
     find out if this is ok *)
  | _ -> bounds
;;

let rec refine_help ty_scrut ctor_is ~ctxt =
  match ty_scrut with
  | Ty.Base _ | Ty.Fn _ -> Envir.Ty_param_refine.bottom
  | Ty.Union ty_scruts ->
    List.fold_right ty_scruts ~init:Envir.Ty_param_refine.top ~f:(fun ty_scrut acc ->
      Envir.Ty_param_refine.meet acc @@ refine_help ty_scrut ctor_is ~ctxt)
  | Ty.Inter ty_scruts ->
    List.fold_right ty_scruts ~init:Envir.Ty_param_refine.bottom ~f:(fun ty_scrut acc ->
      Envir.Ty_param_refine.join acc @@ refine_help ty_scrut ctor_is ~ctxt)
    (* TODO(mjt) what does this mean? Should we also be yielding a
       type refinement in this case since we can refine the type parameters
       bound in the existential? This feels right - we should be able
       to refine then open and expect the same result as opening then refining.
       ∃ T1. I<T1> <~~ C<T>
    *)
  | Ty.Exists { body; _ } -> refine_help body ctor_is ~ctxt
  | Ty.Generic generic -> refine_generic generic ctor_is ~ctxt
  | Ty.Ctor ctor_scrut -> refine_ctor ~ctor_scrut ~ctor_is ~ctxt

and refine_generic generic ctor_is ~ctxt =
  (* Find the existing, possibly refined bounds of the generic in scrutinee
     position *)
  match Ctxt.param_bounds ctxt generic with
  | None -> Envir.Ty_param_refine.bottom
  | Some Ty.Param_bounds.{ lower_bound; upper_bound } ->
    let lb = refine_help (Option.value ~default:Ty.nothing lower_bound) ctor_is ~ctxt
    and ub = refine_help (Option.value ~default:Ty.mixed upper_bound) ctor_is ~ctxt in
    (* TODO(mjt) check this! *)
    Envir.Ty_param_refine.meet lb ub

and refine_ctor ~ctor_scrut ~ctor_is ~ctxt =
  let Ty.Ctor.{ ctor = at; args = args_scrut } = ctor_scrut in
  (* Find the instantiation of the refining subtype at the scrutinee supertype *)
  match Ctxt.up ctxt ~of_:ctor_is ~at with
  (* The refining type was not a subtype of the scrutinee; no refinement *)
  | None -> Envir.Ty_param_refine.bottom
  (* If the refining type was a subtype, we get back the list of types for
     its instantiation at the supertype and any implied bounds. Since these
     must be equal we unify the bounds
  *)
  | Some (args_is, bounds) ->
    Envir.Ty_param_refine.bounds
    @@ List.fold2_exn args_is args_scrut ~init:bounds ~f:(fun bounds is_ scrut -> unify ~is_ ~scrut bounds)
;;

let bind_quants ty_param_env quants =
  List.fold_left quants ~init:ty_param_env ~f:(fun env Ty.Param.{ ident; param_bounds } ->
    let generic = Ty.Generic.Generic ident in
    Envir.Ty_param.bind env generic param_bounds)
;;

let rec get_ctor ty_is ~ctxt =
  match ty_is with
  | Ty.Exists { body; quants } ->
    (match get_ctor body ~ctxt with
     | None -> None
     | Some (ctor, ctxt, delta) ->
       let delta = bind_quants delta quants in
       Some (ctor, ctxt, delta))
  | Ty.Ctor ctor -> Some (ctor, ctxt, Envir.Ty_param.empty)
  | _ -> None
;;

let promote_param_bounds Ty.Param_bounds.{ lower_bound; upper_bound } delta ~oracle =
  let lower_bound = Option.map lower_bound ~f:(fun ty -> Exposure.demote_exn ty delta ~oracle)
  and upper_bound = Option.map upper_bound ~f:(fun ty -> Exposure.promote_exn ty delta ~oracle) in
  Ty.Param_bounds.{ lower_bound; upper_bound }
;;

let promote_rfn rfn delta ~oracle =
  if Envir.Ty_param_refine.is_empty delta
  then rfn
  else Envir.Ty_param_refine.map rfn ~f:(fun param_bounds -> promote_param_bounds param_bounds delta ~oracle)
;;

let refine ~ty_scrut ~ty_is ~ctxt =
  Option.value_map ~default:Envir.Ty_param_refine.bottom ~f:(fun (ctor_is, ctxt, delta) ->
    let rfn_env = refine_help ty_scrut ctor_is ~ctxt:Ctxt.(merge_disjoint_exn ctxt delta) in
    let Ctxt.{ oracle; _ } = ctxt in
    promote_rfn rfn_env delta ~oracle)
  @@ get_ctor ty_is ~ctxt
;;

module Example = struct
  let print_rfn rfn = Envir.Ty_param_refine.pp Format.std_formatter rfn

  (* ~~ UPPER BOUND, UNIFY ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
     Given 
     class E<T as B> implements I<T> { ... }
     Γ, nothing <: T <: mixed, $x:I<T>
     
     if we have an expression `$x is E<Texists>` so we open the existential to bind Texists
     Γ, nothing <: T <: mixed, $x:I<T>, nothing <: Texists <: B
      
     then we refine I<T> <~~ E<Texists> and expect 
     T <: Texists <: T
     T <: B
  *)
  let ctxt1, ty_scrut1, ty_is1, rfn1 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let tp_texists = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "Texists") in
    let ty_param = Envir.Ty_param.(bind empty tp_t Ty.Param_bounds.top) in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut = Ty.ctor Identifier.Ctor.(Ctor "I") [ Ty.Generic tp_t ]
    and ty_is = Ty.ctor Identifier.Ctor.(Ctor "E") [ Ty.Generic tp_texists ] in
    let rfn = refine ~ty_scrut ~ty_is ~ctxt in
    ctxt, ty_scrut, ty_is, rfn
  ;;

  (* ~~ SOLVE PARAM ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     class F implements J<bool>
     Γ, nothing <: T <: mixed, $x:J<T>

     if we have an expression `$x is F`,  we refine J<T> <~~ F and expect

     bool <: T <: bool
  *)
  let ctxt2, ty_scrut2, ty_is2 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let ty_param = Envir.Ty_param.(bind empty tp_t Ty.Param_bounds.top) in
    ( Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    , Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t ]
    , Ty.ctor Identifier.Ctor.(Ctor "F") [] )
  ;;

  let rfn2 = refine ~ty_scrut:ty_scrut2 ~ty_is:ty_is2 ~ctxt:ctxt2

  (* ~~ LOWER BOUND, UNIFY ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     class D<T super A> implements M<T> {}
     Γ, nothing <: T <: mixed, $x:M<T>

     if we have an expression `$x is D<Texist>` we open the existential to get  
     Γ, nothing <: T <: mixed, $x:M<T>, A <: Texists <: mixed

     then we refine M<T> <~~ D<Texists> and expect no refinement

     A <: T <: mixed
     T <: Texists <: T

     I don't think we can currently do this in Hack - does it make sense?
  *)
  let ctxt3, ty_scrut3, ty_is3, rfn3 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let tp_texists = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "Texists") in
    let ty_a = Ty.ctor Identifier.Ctor.(Ctor "A") [] in
    let ty_param =
      Envir.Ty_param.(
        bind (bind empty tp_texists @@ Ty.Param_bounds.create ~lower_bound:ty_a ()) tp_t Ty.Param_bounds.top)
    in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut = Ty.ctor Identifier.Ctor.(Ctor "M") [ Ty.Generic tp_t ]
    and ty_is = Ty.ctor Identifier.Ctor.(Ctor "D") [ Ty.Generic tp_texists ] in
    let rfn = refine ~ty_scrut ~ty_is ~ctxt in
    ctxt, ty_scrut, ty_is, rfn
  ;;

  (* ~~ UNION, COINCIDENT POINTS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     class AA implements I<bool>, J<bool> {}
     Γ, nothing <: T <: mixed, $x:(I<T> | J<T>)

     if we have an expression `$x is AA` we refine (I<T> | J<T>) <~~ AA and expect 

     bool <: T <: bool
  *)
  let ctxt4, ty_scrut4, ty_is4, rfn4 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let ty_param = Envir.Ty_param.(bind empty tp_t Ty.Param_bounds.top) in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut =
      Ty.union
        [ Ty.ctor Identifier.Ctor.(Ctor "I") [ Ty.Generic tp_t ]
        ; Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t ]
        ]
    and ty_is = Ty.ctor Identifier.Ctor.(Ctor "AA") [] in
    let rfn = refine ~ty_scrut ~ty_is ~ctxt in
    ctxt, ty_scrut, ty_is, rfn
  ;;

  (* ~~ UNION, NON-COINCIDENT POINTS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     class BB implements I<bool>, J<int> {}
     Γ, nothing <: T <: mixed, $x:(I<T> | J<T>)

     if we have an expression `$x is BB` we refine (I<T> | J<T>) <~~ BB and expect 

     (bool | int) <: T <: (bool & int) == (bool | int) <: T <: nothing == ⊥
  *)
  let ctxt5, ty_scrut5, ty_is5, rfn5 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let ty_param = Envir.Ty_param.(bind empty tp_t Ty.Param_bounds.top) in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut =
      Ty.union
        [ Ty.ctor Identifier.Ctor.(Ctor "I") [ Ty.Generic tp_t ]
        ; Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t ]
        ]
    and ty_is = Ty.ctor Identifier.Ctor.(Ctor "BB") [] in
    let rfn = refine ~ty_scrut ~ty_is ~ctxt in
    ctxt, ty_scrut, ty_is, rfn
  ;;

  (* ~~ UNION, INTERSECTING BOUDNS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     class CC<T super int as (int | string)> implements I<int>, J<T> {}
     Γ, nothing <: T <: mixed, $x:(I<T> | J<T>)

     if we have an expression `$x is CC<Texists>` we open the existential to get 
     Γ, nothing <: T <: mixed, $x:(I<T> | J<T>), int <: Texists <: (int | string)
      
     then we refine (I<T> | J<T>) <~~ CC<Texists> and expect 

     (int | int) <: T <: ((int | string) & int) == int <: T <: int
  *)
  let ctxt6, ty_scrut6, ty_is6, rfn6 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let tp_texists = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "Texist") in
    let ty_param =
      Envir.Ty_param.(
        bind (bind empty tp_t Ty.Param_bounds.top) tp_texists
        @@ Ty.Param_bounds.create ~lower_bound:Ty.int ~upper_bound:Ty.(union [ int; string ]) ())
    in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut =
      Ty.union
        [ Ty.ctor Identifier.Ctor.(Ctor "I") [ Ty.Generic tp_t ]
        ; Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t ]
        ]
    and ty_is = Ty.ctor Identifier.Ctor.(Ctor "CC") [ Ty.Generic tp_texists ] in
    let rfn = refine ~ty_scrut ~ty_is ~ctxt in
    ctxt, ty_scrut, ty_is, rfn
  ;;

  (* ~~ SOLVE PARAM VIA BOUND ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     interface J<T> {}
     class F implements J<bool>

     and some function 
     function foo<T1 as J<T2>, T2>(T1 $x): void { ... }

     we have
     Γ, nothing <: T2 <: mixed, nothing <: T1 <: J<T2>, $x:T1

     if we have an expression `$x is F`,  we refine T1 <~~ F and expect

     bool <: T2 <: bool
  *)
  let ctxt7, ty_scrut7, ty_is7, rfn7 =
    let tp_t1 = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T1") in
    let tp_t2 = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T2") in
    let ty_param =
      Envir.Ty_param.(
        bind (bind empty tp_t2 Ty.Param_bounds.top) tp_t1
        @@ Ty.Param_bounds.create ~upper_bound:(Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t2 ]) ())
    in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut = Ty.Generic tp_t1
    and ty_is = Ty.ctor Identifier.Ctor.(Ctor "F") [] in
    let rfn = refine ~ty_scrut ~ty_is ~ctxt in
    ctxt, ty_scrut, ty_is, rfn
  ;;
end
