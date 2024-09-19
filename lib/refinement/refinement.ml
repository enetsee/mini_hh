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
  aux ress @@ Ok []
;;

let sequence_any ress =
  let rec aux ress refns errs =
    match ress with
    | [] when List.is_empty refns -> Error errs
    | [] -> Ok refns
    | Ok refn_next :: ress -> aux ress (refn_next :: refns) errs
    | Error err_next :: ress -> aux ress refns (err_next :: errs)
  in
  aux ress [] []
;;

let rec refine ~ty_scrut ~ty_test ~ctxt : (Ty.t * Envir.Ty_param_refine.t, Err.t) result =
  match ty_scrut, ty_test with
  | _, Ty.Exists { quants; body } ->
    (* Bind the quantifiers in the type parameter env
       TODO(mjt) these need to be fresh wrt to the enclosing context
    *)
    let ctxt = Ctxt.bind_all ctxt quants in
    (* Refine the body in this context *)
    refine ~ty_scrut ~ty_test:body ~ctxt
    |> Result.map ~f:(fun (body, refn) ->
      (* Apply the type parameter refinements to the quantifiers *)
      let quants =
        List.map quants ~f:(fun Ty.Param.{ ident; param_bounds } ->
          let bounds_delta = Envir.Ty_param_refine.find refn (Ty.Generic.Generic ident) in
          let param_bounds = Ty.Param_bounds.meet param_bounds bounds_delta in
          Ty.Param.{ ident; param_bounds })
      in
      (* Unbind the quantifiers in the refinement *)
      let refn =
        Envir.Ty_param_refine.unbind_all refn
        @@ List.map quants ~f:(fun Ty.Param.{ ident; _ } -> Ty.Generic.Generic ident)
      in
      let ty_test = Ty.Exists { quants; body } in
      ty_test, refn)
  | Ty.Union ty_scruts, _ -> refine_union_scrut ~ty_scruts ~ty_test ~ctxt
  | Ty.Inter ty_scruts, _ -> refine_inter_scrut ~ty_scruts ~ty_test ~ctxt
  | Ty.Ctor ctor_scrut, Ty.Ctor ctor_test -> refine_ctor ~ctor_scrut ~ctor_test ~ctxt
  | _, _ ->
    (* TODO(mjt) handle existentials in scrutinee and test position
       TODO(mjt) integrate with subtyping so we can eliminate impossible refinements *)
    Ok (ty_test, Envir.Ty_param_refine.top)

(** Refining a union type means we can eliminate the elements which are not
    supertypes of the test type - refinement is an assertion that
    we have the test type in hand and this can only be true for the parts of
    the union which are supertypes. Once we find the refinements resulting
    from the 'good' elements, we find the meet to find what requirements
    are common to all *)
and refine_union_scrut ~ty_scruts ~ty_test ~ctxt =
  Result.map ~f:(fun xs ->
    let tys, refns = List.unzip xs in
    Ty.union tys, Envir.Ty_param_refine.meet_many refns)
  @@ Result.map_error ~f:Err.multiple
  @@ sequence_any
  @@ List.map ty_scruts ~f:(fun ty_scrut -> refine ~ty_scrut ~ty_test ~ctxt)

(** Refining an intersection type doesn't let us elminate any element - they
    must all be supertypes of the test type - refinement is an assertion that
    we have the test type in hand so we must be able to view it at all of the
    types in the intersection *)
and refine_inter_scrut ~ty_scruts ~ty_test ~ctxt =
  Result.map ~f:(fun xs ->
    let tys, refns = List.unzip xs in
    Ty.inter tys, Envir.Ty_param_refine.meet_many refns)
  @@ Result.map_error ~f:Err.multiple
  @@ sequence_all
  @@ List.map ty_scruts ~f:(fun ty_scrut -> refine ~ty_scrut ~ty_test ~ctxt)

and refine_ctor ~ctor_scrut ~ctor_test ~ctxt =
  let oracle = ctxt.Ctxt.oracle in
  match Oracle.up oracle ~of_:ctor_test ~at:ctor_scrut.ctor with
  | None ->
    (* The constructor in test position does not have the constructor in scrutinee position
       as a superclass so we can't refine any type parameters. It's still possible that this test will
       pass e.g.
       
       interface I {}
       interface J {}
       class C implements I , J {}

       function foo(I $i): void {
         if($i is J) { ... }
       }
      
      function call(C $c): void {
         foo($c);
      }
    *)
    Error (Err.not_a_subclass ctor_scrut.ctor ctor_test.ctor)
  | Some args_up ->
    (* We now have the type arguments for the test constructor seen at its instantiation
    *)
    let variance = Option.value_exn (Oracle.param_variances_opt oracle ~ctor:ctor_scrut.ctor) in
    Result.map ~f:(fun xs ->
      let _, refns = List.unzip xs in
      Ty.Ctor ctor_test, Envir.Ty_param_refine.meet_many refns)
    @@ Result.map_error ~f:Err.multiple
    @@ sequence_all
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
      ( ty_test
      , Envir.Ty_param_refine.bounds
        @@ Ty.Generic.Map.of_alist_exn
             [ g_scrut, Option.value_exn (Ctxt.param_bounds ctxt g_test)
             ; g_test, Ty.Param_bounds.create ~lower_bound:ty_scrut ~upper_bound:ty_scrut ()
             ] )
  | Ty.Generic g_scrut, _, _ ->
    (* We have a concrete type in test position so refine the bounds of the generic to this type *)
    Ok
      ( ty_test
      , Envir.Ty_param_refine.singleton g_scrut @@ Ty.Param_bounds.create ~lower_bound:ty_test ~upper_bound:ty_test ()
      )
  | _, Ty.Generic g_test, Variance.Cov ->
    (* We have a concrete type in scrutinee position and a covariant generic in test position so we can refine it
       further by adding the concrete type as an upper bound *)
    Ok (ty_test, Envir.Ty_param_refine.singleton g_test @@ Ty.Param_bounds.create ~upper_bound:ty_scrut ())
  | _, Ty.Generic g_test, Variance.Contrav ->
    Ok (ty_test, Envir.Ty_param_refine.singleton g_test @@ Ty.Param_bounds.create ~lower_bound:ty_scrut ())
  | _, Ty.Generic g_test, Variance.Inv ->
    Ok
      ( ty_test
      , Envir.Ty_param_refine.singleton g_test @@ Ty.Param_bounds.create ~lower_bound:ty_scrut ~upper_bound:ty_scrut ()
      )
    (* We have two concrete types so we need to recurse into them to discover refinements on any nested generic *)
  | _, _, Variance.Cov -> refine ~ty_scrut ~ty_test ~ctxt
  | _, _, Variance.Contrav -> refine ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt
  | _, _, Variance.Inv ->
    Result.map ~f:(fun xs ->
      let tys, refns = List.unzip xs in
      List.hd_exn tys, Envir.Ty_param_refine.meet_many refns)
    @@ Result.map_error ~f:Err.multiple
    @@ sequence_all [ refine ~ty_scrut ~ty_test ~ctxt; refine ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt ]
;;
