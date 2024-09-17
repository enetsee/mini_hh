open Core
open Common
module Ctxt = Ctxt

module Err = struct
  type t =
    | Not_a_subclass of Identifier.Ctor.t * Identifier.Ctor.t
    | Multiple of t list
  [@@deriving variants, eq, show]
end

let sequence_all ress =
  let rec aux ress acc =
    match acc, ress with
    | _, [] -> acc
    | Ok refn_acc, Ok refn_next :: ress ->
      let acc = Ok (refn_next :: refn_acc) in
      aux ress acc
    | Error _, Ok _ :: ress -> aux ress acc
    | Ok _, Error error :: ress ->
      let acc = Error [ error ] in
      aux ress acc
    | Error err_acc, Error err_next :: ress ->
      let acc = Error (err_next :: err_acc) in
      aux ress acc
  in
  Result.map ~f:Envir.Ty_param_refine.join_many @@ Result.map_error ~f:Err.multiple @@ aux ress @@ Ok []
;;

let sequence_any ress =
  let rec aux ress refns errs =
    match ress with
    | [] when List.is_empty errs -> Ok refns
    | [] -> Error errs
    | Ok refn_next :: ress -> aux ress (refn_next :: refns) errs
    | Error err_next :: ress -> aux ress refns (err_next :: errs)
  in
  Result.map ~f:Envir.Ty_param_refine.meet_many @@ Result.map_error ~f:Err.multiple @@ aux ress [] []
;;

let combine ress =
  let rec aux ress acc =
    match acc, ress with
    | _, [] -> acc
    | Ok refn_acc, Ok refn_next :: ress ->
      let acc = Ok (refn_next :: refn_acc) in
      aux ress acc
    | Error _, Ok _ :: ress -> aux ress acc
    | Ok _, Error error :: ress ->
      let acc = Error [ error ] in
      aux ress acc
    | Error err_acc, Error err_next :: ress ->
      let acc = Error (err_next :: err_acc) in
      aux ress acc
  in
  Result.map ~f:Envir.Ty_param_refine.meet_many @@ Result.map_error ~f:Err.multiple @@ aux ress @@ Ok []
;;

let rec refine ~ty_scrut ~ty_test ~ctxt =
  match ty_scrut, ty_test with
  | Ty.Union ty_scruts, _ -> refine_union_scrut ~ty_scruts ~ty_test ~ctxt
  | Ty.Inter ty_scruts, _ -> refine_inter_scrut ~ty_scruts ~ty_test ~ctxt
  | Ty.Ctor ctor_scrut, Ty.Ctor ctor_test -> refine_ctor ~ctor_scrut ~ctor_test ~ctxt
  | _, _ ->
    (* TODO(mjt) handle existentials in scrutinee and test position
       TODO(mjt) integrate with subtyping so we can eliminate impossible refinements *)
    Ok Envir.Ty_param_refine.top

and refine_union_scrut ~ty_scruts ~ty_test ~ctxt =
  sequence_any @@ List.map ty_scruts ~f:(fun ty_scrut -> refine ~ty_scrut ~ty_test ~ctxt)

and refine_inter_scrut ~ty_scruts ~ty_test ~ctxt =
  sequence_all @@ List.map ty_scruts ~f:(fun ty_scrut -> refine ~ty_scrut ~ty_test ~ctxt)

and refine_ctor ~ctor_scrut ~ctor_test ~ctxt =
  let oracle = ctxt.Ctxt.oracle in
  match Oracle.up oracle ~of_:ctor_test ~at:ctor_scrut.ctor with
  | None ->
    (* The constructor in test position does not have the constructor in scrutinee position
       as a superclass so this refinement is impossible *)
    Error (Err.not_a_subclass ctor_scrut.ctor ctor_test.ctor)
  | Some args_up ->
    (* We now have the type arguments for the test constructor seen at its instantiation
    *)
    let variance = Option.value_exn (Oracle.param_variances_opt oracle ~ctor:ctor_scrut.ctor) in
    combine
    @@ List.map3_exn ctor_scrut.args args_up variance ~f:(fun ty_scrut ty_test variance ->
      refine_ctor_arg ~ty_scrut ~ty_test variance ~ctxt)

and refine_ctor_arg ~ty_scrut ~ty_test variance ~ctxt =
  match ty_scrut, ty_test, variance with
  | Ty.Generic g_scrut, Ty.Generic g_test, _ ->
    (* Two generics appearing in the same position means they must be equal. To reflect this we need our refinement
       to:
       1) reflect that the bounds of the generic in scrutinee are refined by the bounds of the generic in test position; and
       2) reflect that the generic in test position is equal to the generic in scrutinee position.
    *)
    Ok
      (Envir.Ty_param_refine.bounds
       @@ Ty.Generic.Map.of_alist_exn
            [ g_scrut, Option.value_exn (Ctxt.param_bounds ctxt g_test)
            ; g_test, Ty.Param_bounds.create ~lower_bound:ty_scrut ~upper_bound:ty_scrut ()
            ])
  | Ty.Generic g_scrut, _, _ ->
    (* We have a concrete type in test position so refine the bounds of the generic to this type *)
    Ok (Envir.Ty_param_refine.singleton g_scrut @@ Ty.Param_bounds.create ~lower_bound:ty_test ~upper_bound:ty_test ())
  | _, Ty.Generic g_test, Variance.Cov ->
    (* We have a concrete type in scrutinee position and a covariant generic in test position so we can refine it
       further by adding the concrete type as an upper bound *)
    Ok (Envir.Ty_param_refine.singleton g_test @@ Ty.Param_bounds.create ~upper_bound:ty_scrut ())
  | _, Ty.Generic g_test, Variance.Contrav ->
    Ok (Envir.Ty_param_refine.singleton g_test @@ Ty.Param_bounds.create ~lower_bound:ty_scrut ())
  | _, Ty.Generic g_test, Variance.Inv ->
    Ok (Envir.Ty_param_refine.singleton g_test @@ Ty.Param_bounds.create ~lower_bound:ty_scrut ~upper_bound:ty_scrut ())
    (* We have two concrete types so we need to recurse into them to discover refinements on any nested generic *)
  | _, _, Variance.Cov -> refine ~ty_scrut ~ty_test ~ctxt
  | _, _, Variance.Contrav -> refine ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt
  | _, _, Variance.Inv -> combine [ refine ~ty_scrut ~ty_test ~ctxt; refine ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt ]
;;

(* let rec refine_help ty_scrut ctor_is ~ctxt =
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
  let bounds, _errs, _cstrs = Down.down ~scrut:ctor_scrut ~is:ctor_is ~acc:Envir.Ty_param_refine in
  failwith ""
;;

(* if Map.is_empty bounds then *)

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
;; *)

(* module Example = struct
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
  let ctxt1, ty_scrut1, ty_test1, rfn1 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let tp_texists = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "Texists") in
    let ty_param = Envir.Ty_param.(bind empty tp_t Ty.Param_bounds.top) in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut = Ty.ctor Identifier.Ctor.(Ctor "I") [ Ty.Generic tp_t ]
    and ty_test = Ty.ctor Identifier.Ctor.(Ctor "E") [ Ty.Generic tp_texists ] in
    let rfn = refine ~ty_scrut ~ty_test ~ctxt in
    ctxt, ty_scrut, ty_test, rfn
  ;;

  (* ~~ SOLVE PARAM ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     class F implements J<bool>
     Γ, nothing <: T <: mixed, $x:J<T>

     if we have an expression `$x is F`,  we refine J<T> <~~ F and expect

     bool <: T <: bool
  *)
  let ctxt2, ty_scrut2, ty_test2 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let ty_param = Envir.Ty_param.(bind empty tp_t Ty.Param_bounds.top) in
    ( Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    , Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t ]
    , Ty.ctor Identifier.Ctor.(Ctor "F") [] )
  ;;

  let rfn2 = refine ~ty_scrut:ty_scrut2 ~ty_test:ty_test2 ~ctxt:ctxt2

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
  let ctxt3, ty_scrut3, ty_test3, rfn3 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let tp_texists = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "Texists") in
    let ty_a = Ty.ctor Identifier.Ctor.(Ctor "A") [] in
    let ty_param =
      Envir.Ty_param.(
        bind (bind empty tp_texists @@ Ty.Param_bounds.create ~lower_bound:ty_a ()) tp_t Ty.Param_bounds.top)
    in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut = Ty.ctor Identifier.Ctor.(Ctor "M") [ Ty.Generic tp_t ]
    and ty_test = Ty.ctor Identifier.Ctor.(Ctor "D") [ Ty.Generic tp_texists ] in
    let rfn = refine ~ty_scrut ~ty_test ~ctxt in
    ctxt, ty_scrut, ty_test, rfn
  ;;

  (* ~~ UNION, COINCIDENT POINTS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     class AA implements I<bool>, J<bool> {}
     Γ, nothing <: T <: mixed, $x:(I<T> | J<T>)

     if we have an expression `$x is AA` we refine (I<T> | J<T>) <~~ AA and expect 

     bool <: T <: bool
  *)
  let ctxt4, ty_scrut4, ty_test4, rfn4 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let ty_param = Envir.Ty_param.(bind empty tp_t Ty.Param_bounds.top) in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut =
      Ty.union
        [ Ty.ctor Identifier.Ctor.(Ctor "I") [ Ty.Generic tp_t ]
        ; Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t ]
        ]
    and ty_test = Ty.ctor Identifier.Ctor.(Ctor "AA") [] in
    let rfn = refine ~ty_scrut ~ty_test ~ctxt in
    ctxt, ty_scrut, ty_test, rfn
  ;;

  (* ~~ UNION, NON-COINCIDENT POINTS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     Given
     class BB implements I<bool>, J<int> {}
     Γ, nothing <: T <: mixed, $x:(I<T> | J<T>)

     if we have an expression `$x is BB` we refine (I<T> | J<T>) <~~ BB and expect 

     (bool | int) <: T <: (bool & int) == (bool | int) <: T <: nothing == ⊥
  *)
  let ctxt5, ty_scrut5, ty_test5, rfn5 =
    let tp_t = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T") in
    let ty_param = Envir.Ty_param.(bind empty tp_t Ty.Param_bounds.top) in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut =
      Ty.union
        [ Ty.ctor Identifier.Ctor.(Ctor "I") [ Ty.Generic tp_t ]
        ; Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t ]
        ]
    and ty_test = Ty.ctor Identifier.Ctor.(Ctor "BB") [] in
    let rfn = refine ~ty_scrut ~ty_test ~ctxt in
    ctxt, ty_scrut, ty_test, rfn
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
  let ctxt6, ty_scrut6, ty_test6, rfn6 =
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
    and ty_test = Ty.ctor Identifier.Ctor.(Ctor "CC") [ Ty.Generic tp_texists ] in
    let rfn = refine ~ty_scrut ~ty_test ~ctxt in
    ctxt, ty_scrut, ty_test, rfn
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
  let ctxt7, ty_scrut7, ty_test7, rfn7 =
    let tp_t1 = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T1") in
    let tp_t2 = Ty.Generic.Generic Identifier.Ty_param.(Ty_param "T2") in
    let ty_param =
      Envir.Ty_param.(
        bind (bind empty tp_t2 Ty.Param_bounds.top) tp_t1
        @@ Ty.Param_bounds.create ~upper_bound:(Ty.ctor Identifier.Ctor.(Ctor "J") [ Ty.Generic tp_t2 ]) ())
    in
    let ctxt = Ctxt.create ~ty_param ~ty_param_refine:Envir.Ty_param_refine.top ~oracle:Oracle.Example.oracle ()
    and ty_scrut = Ty.Generic tp_t1
    and ty_test = Ty.ctor Identifier.Ctor.(Ctor "F") [] in
    let rfn = refine ~ty_scrut ~ty_test ~ctxt in
    ctxt, ty_scrut, ty_test, rfn
  ;;
end *)
