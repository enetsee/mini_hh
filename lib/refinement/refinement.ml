open Core
open Common
open Reporting
module Ctxt = Ctxt

type t =
  | Intersect_with of Reporting.Prov.t * Ty.t
  | Replace_with of Ty.t * Envir.Ty_param_refine.t
[@@deriving compare, eq, show, variants]

let sequence_all ress =
  match List.partition_result ress with
  | refns, [] -> Ok refns
  | _, errs -> Error errs
;;

let sequence_any ress =
  match List.partition_result ress with
  | [], errs -> Error errs
  | refns, _ -> Ok refns
;;

let combine ty_scruts refns =
  List.fold2_exn ty_scruts refns ~init:([], []) ~f:(fun (tys, refns) ty_scrut refn ->
    match refn with
    | Replace_with (ty, refn) -> ty :: tys, refn :: refns
    | Intersect_with (prov, ty_test) -> Ty.inter [ ty_scrut; ty_test ] ~prov :: tys, refns)
;;

let combine_one ty_scrut refns =
  List.fold_left refns ~init:([], []) ~f:(fun (tys, refns) refn ->
    match refn with
    | Replace_with (ty, refn) -> ty :: tys, refn :: refns
    | Intersect_with (prov, ty_test) -> Ty.inter [ ty_scrut; ty_test ] ~prov :: tys, refns)
;;

let rec refine ~ty_scrut ~ty_test ~ctxt : (t, Subtyping.Err.t) result =
  match Ty.prj ty_scrut, Ty.prj ty_test with
  | _, (_, Ty.Node.Generic _) -> failwith "Nope"
  (* -- Existentials -- *)
  | (prov_scrut, Ty.Node.Exists exists_scrut), _ -> refine_existential_scrut prov_scrut exists_scrut ty_test ~ctxt
  | _, (prov_test, Ty.Node.Exists exists_test) -> refine_existential_test ty_scrut prov_test exists_test ~ctxt
  (* -- Unions & intersections *)
  | _, (prov_test, Ty.Node.Union ty_tests) -> refine_union_test prov_test ~ty_tests ~ty_scrut ~ctxt
  | _, (prov_test, Ty.Node.Inter ty_tests) -> refine_inter_test prov_test ~ty_tests ~ty_scrut ~ctxt
  | (prov_scrut, Ty.Node.Union ty_scruts), _ -> refine_union_scrut prov_scrut ~ty_scruts ~ty_test ~ctxt
  | (prov_scrut, Ty.Node.Inter ty_scruts), _ -> refine_inter_scrut prov_scrut ~ty_scruts ~ty_test ~ctxt
  (* -- Constructors -- *)
  | (prov_scrut, Ty.Node.Ctor ctor_scrut), (prov_test, Ty.Node.Ctor ctor_test) ->
    refine_ctor ~ctor_scrut ~ctor_test ~prov_scrut ~prov_test ~ctxt
  (* -- Everything else -- *)
  | (prov_scrut, _), (prov_test, _) ->
    let prov = Reporting.Prov.refines ~prov_scrut ~prov_test in
    (* TODO(mjt) integrate with subtyping so we can eliminate impossible refinements *)
    Ok (Intersect_with (prov, ty_test))

(* ~~ Refine existentials ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

and refine_existential_scrut prov_exists Ty.Exists.{ quants; body } ty_test ~ctxt =
  let ctxt, generics = Ctxt.fresh_generics ctxt (List.length quants) in
  let subst, quants =
    let subst, quants =
      List.unzip
      @@ List.map2_exn quants generics ~f:(fun Ty.Param.{ name; param_bounds } fresh_name ->
        (name, Ty.generic Prov.empty fresh_name), Ty.Param.{ name = fresh_name; param_bounds })
    in
    let subst = Name.Ty_param.Map.of_alist_exn subst in
    subst, quants
  in
  let body = Ty.apply_subst body ~subst ~combine_prov:(fun p _ -> p) in
  let ctxt = Ctxt.bind_all ctxt quants in
  (* Refine the body in this context *)
  let body_refn = refine ~ty_scrut:body ~ty_test ~ctxt in
  Result.map body_refn ~f:(function
    | Replace_with (body, refn) ->
      let quants =
        List.map quants ~f:(fun Ty.Param.{ name; param_bounds } ->
          let param_bounds =
            match Envir.Ty_param_refine.find refn name with
            | Envir.Ty_param_refine.Bounds bounds_delta ->
              (* TODO(mjt): find an example where we haven't solved and figure out if we actually do need to meet here *)
              Ty.Param_bounds.meet param_bounds bounds_delta ~prov:prov_exists
            | Envir.Ty_param_refine.Bounds_top -> param_bounds
            | Envir.Ty_param_refine.Bounds_bottom -> Ty.Param_bounds.bottom prov_exists
          in
          Ty.Param.{ name; param_bounds })
      in
      (* 2) Unbind the quantifiers in the refinement *)
      let refn = Envir.Ty_param_refine.unbind_all refn @@ List.map quants ~f:(fun Ty.Param.{ name; _ } -> name) in
      (* 3) Pack the existential *)
      let ty_test = Ty.exists ~quants ~body prov_exists in
      Replace_with (ty_test, refn)
    | Intersect_with (prov, body') ->
      (* In the case that we couldn't determine the body was a subtype of the scrutinee (and we therefore have no
         type parameter refinement) we need to intersect the body with the scrutinee type before repacking. Since
         there is no refinement the quantifiers are unchanged and there is nothing to unbind *)
      let body = Ty.inter ~prov [ body; body' ] in
      let ty_test = Ty.exists ~quants ~body prov_exists in
      Replace_with (ty_test, Envir.Ty_param_refine.top))

and refine_existential_test ty_scrut prov_exists Ty.Exists.{ quants; body } ~ctxt =
  let ctxt, generics = Ctxt.fresh_generics ctxt (List.length quants) in
  let subst, quants =
    let subst, quants =
      List.unzip
      @@ List.map2_exn quants generics ~f:(fun Ty.Param.{ name; param_bounds } fresh_name ->
        (name, Ty.generic Prov.empty fresh_name), Ty.Param.{ name = fresh_name; param_bounds })
    in
    let subst = Name.Ty_param.Map.of_alist_exn subst in
    subst, quants
  in
  let body = Ty.apply_subst body ~subst ~combine_prov:(fun p _ -> p) in
  let ctxt = Ctxt.bind_all ctxt quants in
  (* Refine the body in this context *)
  let body_refn = refine ~ty_scrut ~ty_test:body ~ctxt in
  Result.map body_refn ~f:(function
    | Replace_with (body, refn) ->
      (* Our refinement of the body gave us a type parameter refinement so we are free to drop the scrutinee type in
         the refined type (i.e. the body is a subtype of the scrutinee type). Before we return this type we need
         to pack the existential with refinements applied to the quantifier and then unbind the quantifiers from the
         type parameter refinement *)

      (* 1) Apply the type parameter refinements to the quantifiers *)
      let quants =
        List.map quants ~f:(fun Ty.Param.{ name; param_bounds } ->
          let param_bounds =
            match Envir.Ty_param_refine.find refn name with
            | Envir.Ty_param_refine.Bounds bounds_delta ->
              (* TODO(mjt): find an example where we haven't solved and figure out if we actually do need to meet here *)
              Ty.Param_bounds.meet param_bounds bounds_delta ~prov:prov_exists
            | Envir.Ty_param_refine.Bounds_top -> param_bounds
            | Envir.Ty_param_refine.Bounds_bottom -> Ty.Param_bounds.bottom prov_exists
          in
          Ty.Param.{ name; param_bounds })
      in
      (* 2) Unbind the quantifiers in the refinement *)
      let refn = Envir.Ty_param_refine.unbind_all refn @@ List.map quants ~f:(fun Ty.Param.{ name; _ } -> name) in
      (* 3) Pack the existential *)
      let ty_test = Ty.exists ~quants ~body prov_exists in
      Replace_with (ty_test, refn)
    | Intersect_with (prov, body) ->
      (* In the case that we couldn't determine the body was a subtype of the scrutinee (and we therefore have no
         type parameter refinement) we need to intersect the body with the scrutinee type before repacking. Since
         there is no refinement the quantifiers are unchanged and there is nothing to unbind *)
      let body = Ty.inter ~prov [ ty_scrut; body ] in
      let ty_test = Ty.exists ~quants ~body prov_exists in
      Replace_with (ty_test, Envir.Ty_param_refine.top))

(* ~~ Refine union types in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Refining a union type means we can eliminate the elements which are not
    supertypes of the test type - refinement is an assertion that
    we have the test type in hand and this can only be true for the parts of
    the union which are supertypes. Once we find the refinements resulting
    from the 'good' elements, we find the meet to find what requirements
    are common to all *)
and refine_union_scrut prov ~ty_scruts ~ty_test ~ctxt =
  Result.map ~f:(fun refns ->
    let tys, refns = combine ty_scruts refns in
    Replace_with (Ty.union tys ~prov, Envir.Ty_param_refine.meet_many refns ~prov))
  @@ Result.map_error ~f:Subtyping.Err.multiple
  @@ sequence_any
  @@ List.map ty_scruts ~f:(fun ty_scrut -> refine ~ty_scrut ~ty_test ~ctxt)

(* ~~ Refine union types in test position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

and refine_union_test prov ~ty_tests ~ty_scrut ~ctxt =
  Result.map ~f:(fun refns ->
    let tys, refns = combine_one ty_scrut refns in
    Replace_with (Ty.union tys ~prov, Envir.Ty_param_refine.join_many refns ~prov))
  @@ Result.map_error ~f:Subtyping.Err.multiple
  @@ sequence_any
  @@ List.map ty_tests ~f:(fun ty_test -> refine ~ty_scrut ~ty_test ~ctxt)

(* ~~ Refine intersection types in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Refining an intersection type doesn't let us elminate any element - they
    must all be supertypes of the test type - refinement is an assertion that
    we have the test type in hand so we must be able to view it at all of the
    types in the intersection *)
and refine_inter_scrut prov ~ty_scruts ~ty_test ~ctxt =
  Result.map ~f:(fun refns ->
    let tys, refns = combine ty_scruts refns in
    Replace_with (Ty.inter tys ~prov, Envir.Ty_param_refine.meet_many refns ~prov))
  @@ Result.map_error ~f:Subtyping.Err.multiple
  @@ sequence_all
  @@ List.map ty_scruts ~f:(fun ty_scrut -> refine ~ty_scrut ~ty_test ~ctxt)

(* ~~ Refine intersection types in test position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and refine_inter_test prov ~ty_tests ~ty_scrut ~ctxt =
  Result.map ~f:(fun refns ->
    let tys, refns = combine_one ty_scrut refns in
    Replace_with (Ty.inter tys ~prov, Envir.Ty_param_refine.meet_many refns ~prov))
  @@ Result.map_error ~f:Subtyping.Err.multiple
  @@ sequence_all
  @@ List.map ty_tests ~f:(fun ty_test -> refine ~ty_scrut ~ty_test ~ctxt)

(* ~~ Refine constructor types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and refine_ctor ~ctor_scrut ~ctor_test ~prov_scrut ~prov_test ~ctxt =
  let oracle = ctxt.Ctxt.oracle in
  let prov = Reporting.Prov.refines ~prov_scrut ~prov_test in
  let Ty.Ctor.{ args = args_scrut; name = name_scrut } = ctor_scrut in
  match Oracle.up oracle ~of_:ctor_test ~at:name_scrut with
  | None ->
    (* The constructor in test position does not have the constructor in 
       scrutinee position as a superclass so we can't refine any type parameters. 
       It's still possible that this test will pass if there is a third class 
       which has both scrutinee and test as a supertype e.g.
       
       interface I {}
       interface J {}
       class C implements I , J {}

       function foo(I $i): void {
         if($i is J) { ... }
       }
      
      function call(C $c): void {
         foo($c);
      }
      
      In this case we need to refine to an intersection with the scrutinee 
      rather than replacing it
    *)
    let node = Ty.Node.Ctor ctor_test in
    let ty = Ty.create ~node ~prov:prov_test () in
    Ok (Intersect_with (prov, ty))
  | Some args_up ->
    (* The test type is a subtype of the scrutinee type and we now have the type
       arguments for the test constructor seen at its instantiation at the
       scrutinee so we can refine each argument
    *)
    (* If the type argument from the scrutinee is not a generic but the type in
       the correponding arugment from the test is a generic we will need to know
       the declared variance of the parameter *)
    let variance = Option.value_exn (Oracle.param_variances_opt oracle ~ctor:ctor_scrut.name) in
    (* We need *)
    Result.map ~f:(fun refns ->
      let args, refns = combine args_scrut refns in
      let ctor_up = Ty.Ctor.create ~name:name_scrut ~args () in
      (* Since we've gone up the a superclass we know we can go back down *)
      let args = Option.value_exn @@ Oracle.down oracle ~of_:ctor_up ~at:ctor_test.name in
      let node = Ty.(Node.ctor Ctor.{ ctor_test with args }) in
      let ty = Ty.create ~node ~prov:prov_test () in
      Replace_with (ty, Envir.Ty_param_refine.meet_many refns ~prov:prov_test))
    @@ Result.map_error ~f:Subtyping.Err.multiple
    @@ sequence_all
    @@ List.map3_exn args_scrut args_up variance ~f:(fun ty_scrut ty_test variance ->
      refine_ctor_arg ~ty_scrut ~ty_test variance ~ctxt)

and refine_ctor_arg ~ty_scrut ~ty_test variance ~ctxt =
  let prov_scrut, node_scrut = Ty.prj ty_scrut
  and prov_test, node_test = Ty.prj ty_test in
  match node_scrut, node_test, variance with
  | Ty.Node.Generic g_scrut, Ty.Node.Generic g_test, _ ->
    (* Two generics appearing in the same position means they must be equal. To reflect this we need our refinement
       to:
       1) reflect that the bounds of the generic in scrutinee are refined by the bounds of the generic in test position; and
       2) reflect that the generic in test position is equal to the generic in scrutinee position.
    *)
    Ok
      (Replace_with
         ( ty_test
         , Envir.Ty_param_refine.bounds
           @@ Name.Ty_param.Map.of_alist_exn
                [ g_scrut, Option.value_exn (Ctxt.param_bounds ctxt g_test)
                ; g_test, Ty.Param_bounds.create ~lower:ty_scrut ~upper:ty_scrut ()
                ] ))
  | Ty.Node.Generic g_scrut, _, _ ->
    (* We have a concrete type in test position so refine the bounds of the generic to this type *)
    Ok
      (Replace_with
         (ty_test, Envir.Ty_param_refine.singleton g_scrut @@ Ty.Param_bounds.create ~lower:ty_test ~upper:ty_test ()))
  | _, Ty.Node.Generic g_test, Variance.Cov ->
    (* We have a concrete type in scrutinee position and a covariant generic in test position so we can refine it
       further by adding the concrete type as an upper bound *)
    Ok
      (Replace_with
         ( ty_test
         , Envir.Ty_param_refine.singleton g_test
           @@ Ty.Param_bounds.create ~upper:ty_scrut ~lower:(Ty.nothing prov_scrut) () ))
  | _, Ty.Node.Generic g_test, Variance.Contrav ->
    Ok
      (Replace_with
         ( ty_test
         , Envir.Ty_param_refine.singleton g_test
           @@ Ty.Param_bounds.create ~lower:ty_scrut ~upper:(Ty.mixed prov_scrut) () ))
  | _, Ty.Node.Generic g_test, Variance.Inv ->
    Ok (Replace_with (ty_test, Envir.Ty_param_refine.singleton g_test @@ Ty.Param_bounds.create_equal ty_scrut))
    (* We have two concrete types so we need to recurse into them to discover refinements on any nested generic *)
  | _, _, Variance.Cov -> refine ~ty_scrut ~ty_test ~ctxt
  | _, _, Variance.Contrav -> refine ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt
  | _, _, Variance.Inv ->
    let prov = Reporting.Prov.refines ~prov_scrut ~prov_test in
    Result.map ~f:(fun refns ->
      let tys, refns = combine [ ty_scrut; ty_scrut ] refns in
      Replace_with (Ty.inter tys ~prov, Envir.Ty_param_refine.meet_many refns ~prov))
    @@ Result.map_error ~f:Subtyping.Err.multiple
    @@ sequence_all [ refine ~ty_scrut ~ty_test ~ctxt; refine ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt ]
;;
