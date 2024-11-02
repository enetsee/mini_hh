open Core
open Common
open Reporting
module Eff = Eff

(* This isn't as strict as it could be since a type parameter refinement can only ever happen if the test type is a
   known subclass of the test type _but_ reusing the existing type refinment type makes things easier *)
type intermediate = Ty.Refinement.t * (Reporting.Prov.t * Ctxt.Ty_param.Refinement.t) option

(* ~~ Helpers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let partition_disjoint rfmts =
  let rec aux rfmts ~k =
    match rfmts with
    | [] -> k ([], [])
    | (rfmt, param_rfmt_opt) :: rfmts ->
      aux rfmts ~k:(fun (rfmts, dsjts) ->
        match rfmt with
        | Ty.Refinement.Disjoint prov -> k (rfmts, prov :: dsjts)
        | _ -> k ((rfmt, param_rfmt_opt) :: rfmts, dsjts))
  in
  aux rfmts ~k:Fn.id
;;

let sequence_all ress =
  match partition_disjoint ress with
  | refns, [] -> Ok refns
  | _, errs -> Error errs
;;

let sequence_any ress =
  match partition_disjoint ress with
  | [], errs -> Error errs
  | refns, _ -> Ok refns
;;

let combine ty_scruts refns =
  List.fold2_exn ty_scruts refns ~init:([], []) ~f:(fun (tys, refns) ty_scrut (rfmt, param_rfmt_opt) ->
    ( Ty.refine ty_scrut ~rfmt :: tys
    , Option.value_map param_rfmt_opt ~default:refns ~f:(fun (_prov, refn) -> refn :: refns) ))
;;

let combine_one ty_scrut refns =
  List.fold_left refns ~init:([], []) ~f:(fun (tys, refns) (rfmt, param_rfmt_opt) ->
    ( Ty.refine ty_scrut ~rfmt :: tys
    , Option.value_map param_rfmt_opt ~default:refns ~f:(fun (_prov, refn) -> refn :: refns) ))
;;

(* ~~ Entrypoint ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let rec refine ~ty_scrut ~ty_test ~ctxt =
  let ty_scrut, ty_test, ctxt = Eff.log_enter_refinement ~ty_scrut ~ty_test ~ctxt_cont:ctxt in
  Eff.log_exit_refinement @@ refine_ty ~ty_scrut ~ty_test ~ctxt

and refine_ty ~ty_scrut ~ty_test ~ctxt =
  let ty_scrut, ty_test, ctxt = Eff.log_enter_refine_ty ~ty_scrut ~ty_test ~ctxt_cont:ctxt in
  Eff.log_exit_refine_ty
  @@
  match Ty.prj ty_scrut, Ty.prj ty_test with
  (* ~~ Top-level generics ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_scrut, Ty.Node.Generic name_scrut), _ -> refine_top_level_generic_scrut prov_scrut name_scrut ty_test ~ctxt
  | _, (prov_test, Ty.Node.Generic name_test) ->
    refine_top_level_generic_test ty_scrut prov_test name_test ~ctxt
    (* ~~ Existentials ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_scrut, Ty.Node.Exists exists_scrut), _ -> refine_existential_scrut prov_scrut exists_scrut ty_test ~ctxt
  | _, (prov_test, Ty.Node.Exists exists_test) -> refine_existential_test ty_scrut prov_test exists_test ~ctxt
  (* ~~ Unions & intersections ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | _, (prov_test, Ty.Node.Union ty_tests) -> refine_union_test prov_test ~ty_tests ~ty_scrut ~ctxt
  | _, (prov_test, Ty.Node.Inter ty_tests) -> refine_inter_test prov_test ~ty_tests ~ty_scrut ~ctxt
  | (prov_scrut, Ty.Node.Union ty_scruts), _ -> refine_union_scrut prov_scrut ~ty_scruts ~ty_test ~ctxt
  | (prov_scrut, Ty.Node.Inter ty_scruts), _ -> refine_inter_scrut prov_scrut ~ty_scruts ~ty_test ~ctxt
  (* ~~ Constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_scrut, Ty.Node.Ctor ctor_scrut), (prov_test, Ty.Node.Ctor ctor_test) ->
    refine_ctor ~ctor_scrut ~ctor_test ~prov_scrut ~prov_test ~ctxt
  (* ~~ Everything else ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* TODO(mjt) I'm fairly sure we can do better for tuples and functions here *)
  | (prov_scrut, _), (prov_test, _) ->
    (match Subtyping.Ask.is_subtype ~ty_sub:ty_scrut ~ty_super:ty_test ~ctxt with
     | Subtyping.Answer.No _err ->
       let prov = Reporting.Prov.refine ~prov_scrut ~prov_test in
       Ty.Refinement.disjoint prov, None
     | _ ->
       (* let subty_res = Subtyping.Ask.is_subtype ~ty_sub:ty_test  ~ty_super:ty_scrut *)
       let prov = Reporting.Prov.refine ~prov_scrut ~prov_test in
       (* TODO(mjt) integrate with subtyping so we can eliminate impossible refinements *)
       Ty.Refinement.intersect_with prov ty_test, None)

(* ~~ Refine top-level generics ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and refine_top_level_generic_test ty_scrut prov_test name_test ~ctxt =
  (* If we have a generic in test position we need the scrutinee to be a subtype
     of its upperbound and a supertype of its lowerbound, otherwise it is disjoint *)
  let prov = Reporting.Prov.refine ~prov_scrut:(Ty.prov_of ty_scrut) ~prov_test in
  let Ty.Param_bounds.{ lower; upper } = Option.value_exn @@ Ctxt.Cont.ty_param_bounds ctxt name_test in
  match
    Subtyping.Ask.(is_subtype ~ty_sub:lower ~ty_super:ty_scrut ~ctxt, is_subtype ~ty_sub:ty_scrut ~ty_super:upper ~ctxt)
  with
  | Subtyping.Answer.No _, _ | _, Subtyping.Answer.No _ -> Ty.Refinement.disjoint prov, None
  | _ ->
    let ty_test = Ty.generic prov_test name_test in
    Ty.Refinement.intersect_with prov ty_test, None

and refine_top_level_generic_scrut prov_scrut name_scrut ty_test ~ctxt =
  let prov = Reporting.Prov.refine ~prov_scrut ~prov_test:(Ty.prov_of ty_test) in
  match name_scrut with
  (* ~~ this in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* If the scrutinee has type [this] then we generate a refinement because
     there is only one thing with type [this] *)
  | Name.Ty_param.This ->
    let ty_scrut = Ty.this prov in
    ( Ty.Refinement.replace_with ty_scrut
    , Some
        ( prov
        , Ctxt.Ty_param.Refinement.singleton Name.Ty_param.this
          @@ Ty.Param_bounds.create ~upper:ty_test ~lower:(Ty.nothing prov) () ) )
  (* ~~ generic in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* If we have a non-this generic in scrutinee position then we can't refine
       the generic but we can refine the type. Consider this case: 
       
       function foo<T as arraykey>(vec<T> $xs) : void {
         $x = $xs[0] // $x: T
         if($x is int) {
          // we learned that one element of the vec is an int but this tells us 
          // nothing about the other elements
         }
       }
  *)
  | _ ->
    let Ty.Param_bounds.{ upper; _ } = Option.value_exn @@ Ctxt.Cont.ty_param_bounds ctxt name_scrut in
    let ty_rfmt, _ = refine_ty ~ty_scrut:upper ~ty_test ~ctxt in
    ty_rfmt, Some (prov, Ctxt.Ty_param.Refinement.empty)
(* ~~ Refine existentials ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

and refine_existential_scrut prov_exists ty_exists ty_test ~ctxt =
  let prov_exists, Ty.Exists.{ quants; body }, ty_test, ctxt =
    Eff.log_enter_refine_existential_scrut prov_exists ty_exists ty_test ctxt
  in
  let generics = Eff.gen_fresh_ty_params (List.length quants) in
  let subst, quants =
    let subst, quants =
      List.unzip
      @@ List.map2_exn quants generics ~f:(fun Ty.Param.{ name = Located.{ elem; span }; param_bounds } fresh_name ->
        (elem, Ty.generic Prov.empty fresh_name), Ty.Param.{ name = Located.{ elem = fresh_name; span }; param_bounds })
    in
    let subst = Name.Ty_param.Map.of_alist_exn subst in
    subst, quants
  in
  let body = Ty.apply_subst body ~subst ~combine_prov:(fun p _ -> p) in
  (* Bind the quantifiers and refine the body in this context *)
  let body_refn =
    let ctxt = Ctxt.Cont.bind_ty_params ctxt quants in
    refine_ty ~ty_scrut:body ~ty_test ~ctxt
  in
  Eff.log_exit_refine_existential_scrut
  @@
  match body_refn with
  | Ty.Refinement.Replace_with body, Some (prov, refn) ->
    let quants =
      List.map quants ~f:(fun Ty.Param.{ name; param_bounds } ->
        let param_bounds =
          match Ctxt.Ty_param.Refinement.find refn name.Located.elem with
          | Ctxt.Ty_param.Refinement.Bounds bounds_delta ->
            (* TODO(mjt): find an example where we haven't solved and figure out if we actually do need to meet here *)
            Ty.Param_bounds.meet param_bounds bounds_delta ~prov:prov_exists
          | Ctxt.Ty_param.Refinement.Bounds_top -> param_bounds
          | Ctxt.Ty_param.Refinement.Bounds_bottom -> Ty.Param_bounds.bottom prov_exists
        in
        Ty.Param.{ name; param_bounds })
    in
    (* 2) Unbind the quantifiers in the refinement *)
    let refn =
      Ctxt.Ty_param.Refinement.unbind_all refn @@ List.map quants ~f:(fun Ty.Param.{ name; _ } -> name.Located.elem)
    in
    (* 3) Pack the existential *)
    let ty_test = Ty.exists ~quants ~body prov_exists in
    Ty.Refinement.replace_with ty_test, Some (prov, refn)
  | Ty.Refinement.Intersect_with (prov, body'), None ->
    (* In the case that we couldn't determine the body was a subtype of the scrutinee (and we therefore have no
       type parameter refinement) we need to intersect the body with the scrutinee type before repacking. Since
       there is no refinement the quantifiers are unchanged and there is nothing to unbind *)
    let body = Ty.inter ~prov [ body; body' ] in
    let ty_test = Ty.exists ~quants ~body prov_exists in
    Replace_with ty_test, Some (prov, Ctxt.Ty_param.Refinement.top)
  | Ty.Refinement.Disjoint _, _ -> body_refn
  (* ~~ If we see these something has gone wrong ~~ *)
  | Ty.Refinement.Replace_with _, None | Ty.Refinement.Intersect_with _, Some _ -> failwith "impossible"

and refine_existential_test ty_scrut prov_test Ty.Exists.{ quants; body } ~ctxt =
  let generics = Eff.gen_fresh_ty_params (List.length quants) in
  let subst, quants =
    let subst, quants =
      List.unzip
      @@ List.map2_exn quants generics ~f:(fun Ty.Param.{ name = Located.{ elem; span }; param_bounds } fresh_name ->
        (elem, Ty.generic Prov.empty fresh_name), Ty.Param.{ name = Located.{ elem = fresh_name; span }; param_bounds })
    in
    let subst = Name.Ty_param.Map.of_alist_exn subst in
    subst, quants
  in
  let body = Ty.apply_subst body ~subst ~combine_prov:(fun p _ -> p) in
  (* Refine the body in this context *)
  let body_refn =
    let ctxt = Ctxt.Cont.bind_ty_params ctxt quants in
    refine_ty ~ty_scrut ~ty_test:body ~ctxt
  in
  match body_refn with
  | Replace_with body, Some (prov, refn) ->
    (* Our refinement of the body gave us a type parameter refinement so we are free to drop the scrutinee type in
       the refined type (i.e. the body is a subtype of the scrutinee type). Before we return this type we need
       to pack the existential with refinements applied to the quantifier and then unbind the quantifiers from the
       type parameter refinement *)

    (* 1) Apply the type parameter refinements to the quantifiers *)
    let quants =
      List.map quants ~f:(fun Ty.Param.{ name; param_bounds } ->
        let param_bounds =
          match Ctxt.Ty_param.Refinement.find refn name.Located.elem with
          | Ctxt.Ty_param.Refinement.Bounds bounds_delta ->
            (* TODO(mjt): find an example where we haven't solved and figure out if we actually do need to meet here *)
            Ty.Param_bounds.meet param_bounds bounds_delta ~prov:prov_test
          | Ctxt.Ty_param.Refinement.Bounds_top -> param_bounds
          | Ctxt.Ty_param.Refinement.Bounds_bottom -> Ty.Param_bounds.bottom prov_test
        in
        Ty.Param.{ name; param_bounds })
    in
    (* 2) Unbind the quantifiers in the refinement *)
    let refn =
      Ctxt.Ty_param.Refinement.unbind_all refn @@ List.map quants ~f:(fun Ty.Param.{ name; _ } -> name.Located.elem)
    in
    (* 3) Pack the existential *)
    let ty_test = Ty.exists ~quants ~body prov_test in
    Ty.Refinement.replace_with ty_test, Some (prov, refn)
  | Intersect_with (prov, body), None ->
    (* In the case that we couldn't determine the body was a subtype of the scrutinee (and we therefore have no
       type parameter refinement) we need to intersect the body with the scrutinee type before repacking. Since
       there is no refinement the quantifiers are unchanged and there is nothing to unbind *)
    let body = Ty.inter ~prov [ ty_scrut; body ] in
    let ty_test = Ty.exists ~quants ~body prov_test in
    Replace_with ty_test, Some (prov, Ctxt.Ty_param.Refinement.top)
  | Ty.Refinement.Disjoint _, _ -> body_refn
  (* ~~ If we see these something has gone wrong ~~ *)
  | Ty.Refinement.Replace_with _, None | Ty.Refinement.Intersect_with _, Some _ -> failwith "impossible"

(* ~~ Refine union types in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Refining a union type means we can eliminate the elements which are not
    supertypes of the test type - refinement is an assertion that
    we have the test type in hand and this can only be true for the parts of
    the union which are supertypes. Once we find the refinements resulting
    from the 'good' elements, we find the meet to find what requirements
    are common to all *)
and refine_union_scrut prov ~ty_scruts ~ty_test ~ctxt =
  let res = sequence_any @@ List.map ty_scruts ~f:(fun ty_scrut -> refine_ty ~ty_scrut ~ty_test ~ctxt) in
  match res with
  | Ok refns ->
    let tys, refns = combine ty_scruts refns in
    Replace_with (Ty.union tys ~prov), Some (prov, Ctxt.Ty_param.Refinement.join_many refns ~prov)
  | Error _provs -> Ty.Refinement.Disjoint prov, None

(* ~~ Refine union types in test position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

and refine_union_test prov ~ty_tests ~ty_scrut ~ctxt =
  let res = sequence_any @@ List.map ty_tests ~f:(fun ty_test -> refine_ty ~ty_scrut ~ty_test ~ctxt) in
  match res with
  | Ok refns ->
    let tys, refns = combine_one ty_scrut refns in
    Replace_with (Ty.union tys ~prov), Some (prov, Ctxt.Ty_param.Refinement.join_many refns ~prov)
  | Error _provs -> Ty.Refinement.Disjoint prov, None

(* ~~ Refine intersection types in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Refining an intersection type doesn't let us elminate any element - they
    must all be supertypes of the test type - refinement is an assertion that
    we have the test type in hand so we must be able to view it at all of the
    types in the intersection *)
and refine_inter_scrut prov ~ty_scruts ~ty_test ~ctxt =
  let res = sequence_all @@ List.map ty_scruts ~f:(fun ty_scrut -> refine_ty ~ty_scrut ~ty_test ~ctxt) in
  match res with
  | Ok refns ->
    let tys, refns = combine ty_scruts refns in
    Replace_with (Ty.inter tys ~prov), Some (prov, Ctxt.Ty_param.Refinement.meet_many refns ~prov)
  | Error _provs -> Ty.Refinement.Disjoint prov, None

(* ~~ Refine intersection types in test position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and refine_inter_test prov ~ty_tests ~ty_scrut ~ctxt =
  let res = sequence_all @@ List.map ty_tests ~f:(fun ty_test -> refine_ty ~ty_scrut ~ty_test ~ctxt) in
  match res with
  | Ok refns ->
    let tys, refns = combine_one ty_scrut refns in
    Replace_with (Ty.inter tys ~prov), Some (prov, Ctxt.Ty_param.Refinement.meet_many refns ~prov)
  | Error _provs -> Ty.Refinement.disjoint prov, None

(* ~~ Refine constructor types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and refine_ctor ~ctor_scrut ~ctor_test ~prov_scrut ~prov_test ~ctxt =
  let prov = Reporting.Prov.refine ~prov_scrut ~prov_test in
  let Ty.Ctor.{ args = args_scrut; name = name_scrut } = ctor_scrut in
  match Eff.ask_up ~of_:ctor_test ~at:name_scrut with
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
    Intersect_with (prov, ty), None
  | Some args_up ->
    (* The test type is a subtype of the scrutinee type and we now have the type
       arguments for the test constructor seen at its instantiation at the
       scrutinee so we can refine each argument
    *)
    (* If the type argument from the scrutinee is not a generic but the type in
       the correponding arugment from the test is a generic we will need to know
       the declared variance of the parameter *)
    let variance = Option.value_exn (Eff.ask_ty_param_variances ctor_scrut.name) in
    (* We need *)
    let res =
      sequence_all
      @@ List.map3_exn args_scrut args_up variance ~f:(fun ty_scrut ty_test variance ->
        refine_ctor_arg ~ty_scrut ~ty_test ~ctxt variance)
    in
    (match res with
     | Ok refns ->
       let _args, refns = combine args_scrut refns in
       (* Since we've gone up the a superclass using the type arguments of the 
         subclass; it's possible that we end up refining the same type argument
         against two different types from the scrutinee e.g.
         
         interface I<T1,T2> {}
         class A<T> implements<T,T> {}

         function blah(I<arraykey,bool $x): void {
           if($x is A<_>) {
             [...]
           }
         }

        Here A `up` I gives us `TA, TA`. Since we have generics in test position
        and concrete types in test position, the refinement happens through the 
        type parameter. This means that whenever the argument is generic we can
        just use the incoming scrutinee type constructor as the result type.

        In the case of a refied type argument we have _equal_ concrete types in 
        test position. Since concrete types can refine type parameters in
        scrutinee position _or_ result in disjointness we are also ok to give 
        the incoming constructor type as the result
       *)
       let node = Ty.Node.Ctor ctor_test in
       let ty = Ty.create ~node ~prov () in
       Replace_with ty, Some (prov, Ctxt.Ty_param.Refinement.meet_many refns ~prov:prov_test)
     | Error _provs -> Ty.Refinement.disjoint prov, None)

and refine_ctor_arg ~ty_scrut ~ty_test ~ctxt variance =
  let prov_scrut, node_scrut = Ty.prj ty_scrut
  and prov_test, node_test = Ty.prj ty_test in
  let prov = Reporting.Prov.refine ~prov_scrut ~prov_test in
  match node_scrut, node_test, variance.elem with
  | Ty.Node.Generic g_scrut, Ty.Node.Generic g_test, _ ->
    (* Two generics appearing in the same position means they must be equal. To reflect this we need our refinement
       to:
       1) reflect that the bounds of the generic in scrutinee are refined by the bounds of the generic in test position; and
       2) reflect that the generic in test position is equal to the generic in scrutinee position.
    *)
    ( Ty.Refinement.Replace_with ty_test
    , Some
        ( prov
        , Ctxt.Ty_param.Refinement.bounds
            [ g_scrut, Option.value_exn (Ctxt.Cont.ty_param_bounds ctxt g_test)
            ; g_test, Ty.Param_bounds.create ~lower:ty_scrut ~upper:ty_scrut ()
            ] ) )
  | Ty.Node.Generic g_scrut, _, _ ->
    (* GADT case - we have a concrete type in test position so refine the bounds of the generic to this type *)
    Replace_with ty_test, Some (prov, Ctxt.Ty_param.Refinement.singleton g_scrut @@ Ty.Param_bounds.create_equal ty_test)
  | _, Ty.Node.Generic g_test, Variance.Cov ->
    (* We have a concrete type in scrutinee position and a covariant generic in test position so we can refine it
       further by adding the concrete type as an upper bound *)
    ( Replace_with ty_test
    , Some
        ( prov
        , Ctxt.Ty_param.Refinement.singleton g_test
          @@ Ty.Param_bounds.create ~upper:ty_scrut ~lower:(Ty.nothing prov_scrut) () ) )
  | _, Ty.Node.Generic g_test, Variance.Contrav ->
    ( Replace_with ty_test
    , Some
        ( prov
        , Ctxt.Ty_param.Refinement.singleton g_test
          @@ Ty.Param_bounds.create ~lower:ty_scrut ~upper:(Ty.mixed prov_scrut) () ) )
  | _, Ty.Node.Generic g_test, Variance.Inv ->
    Replace_with ty_test, Some (prov, Ctxt.Ty_param.Refinement.singleton g_test @@ Ty.Param_bounds.create_equal ty_scrut)
    (* We have two concrete types so we need to recurse into them to discover refinements on any nested generic *)
  | _, _, Variance.Cov -> refine_ty ~ty_scrut ~ty_test ~ctxt
  | _, _, Variance.Contrav -> refine_ty ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt
  | _, _, Variance.Inv ->
    let res =
      sequence_all [ refine_ty ~ty_scrut ~ty_test ~ctxt; refine_ty ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt ]
    in
    (match res with
     | Ok refns ->
       let tys, refns = combine [ ty_scrut; ty_scrut ] refns in
       Replace_with (Ty.inter tys ~prov), Some (prov, Ctxt.Ty_param.Refinement.meet_many refns ~prov)
     | Error _provs -> Ty.Refinement.disjoint prov, None)
;;
