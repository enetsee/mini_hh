open Core
open Common
open Reporting
module Eff = Eff

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
  List.fold2_exn
    ty_scruts
    refns
    ~init:([], [])
    ~f:(fun (tys, refns) ty_scrut (rfmt, param_rfmt_opt) ->
      ( Ty.refine ty_scrut ~rfmt :: tys
      , Option.value_map param_rfmt_opt ~default:refns ~f:(fun (_prov, refn) ->
          refn :: refns) ))
;;

let combine_one ty_scrut refns =
  List.fold_left
    refns
    ~init:([], [])
    ~f:(fun (tys, refns) (rfmt, param_rfmt_opt) ->
      ( Ty.refine ty_scrut ~rfmt :: tys
      , Option.value_map param_rfmt_opt ~default:refns ~f:(fun (_prov, refn) ->
          refn :: refns) ))
;;

(* ~~ Entrypoint ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let rec refine ~ty_scrut ~ty_test ~ctxt =
  let ty_scrut, ty_test, ctxt =
    Eff.log_enter_refinement ~ty_scrut ~ty_test ~ctxt_cont:ctxt
  in
  Eff.log_exit_refinement @@ refine_ty ~ty_scrut ~ty_test ~ctxt

and refine_ty ~ty_scrut ~ty_test ~ctxt =
  let ty_scrut, ty_test, ctxt =
    Eff.log_enter_ty ~ty_scrut ~ty_test ~ctxt_cont:ctxt
  in
  Eff.log_exit_ty
  @@
  match Ty.prj ty_scrut, Ty.prj ty_test with
  (* ~~ Top-level generics ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_scrut, Ty.Node.Generic name_scrut), _ ->
    refine_top_level_generic_scrut prov_scrut name_scrut ty_test ~ctxt
  | _, (prov_test, Ty.Node.Generic name_test) ->
    refine_top_level_generic_test ty_scrut prov_test name_test ~ctxt
  (* ~~ Existentials ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_scrut, Ty.Node.Exists exists_scrut), _ ->
    refine_existential_scrut prov_scrut exists_scrut ty_test ~ctxt
  | _, (prov_test, Ty.Node.Exists exists_test) ->
    refine_existential_test ty_scrut prov_test exists_test ~ctxt
  (* ~~ Unions & intersections ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | _, (prov_test, Ty.Node.Union ty_tests) ->
    refine_union_test prov_test ~ty_tests ~ty_scrut ~ctxt
  | _, (prov_test, Ty.Node.Inter ty_tests) ->
    refine_inter_test prov_test ~ty_tests ~ty_scrut ~ctxt
  | (prov_scrut, Ty.Node.Union ty_scruts), _ ->
    refine_union_scrut prov_scrut ~ty_scruts ~ty_test ~ctxt
  | (prov_scrut, Ty.Node.Inter ty_scruts), _ ->
    refine_inter_scrut prov_scrut ~ty_scruts ~ty_test ~ctxt
  (* ~~ Constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (prov_scrut, Ty.Node.Ctor ctor_scrut), (prov_test, Ty.Node.Ctor ctor_test)
    -> refine_ctor ~ctor_scrut ~ctor_test ~prov_scrut ~prov_test ~ctxt
  (* ~~ Everything else ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* TODO(mjt) I'm fairly sure we can do better for tuples and functions here *)
  | (prov_scrut, _), (prov_test, _) ->
    let prov = Reporting.Prov.refine ~prov_scrut ~prov_test in
    (match
       Subtyping.Ask.is_subtype ~ty_sub:ty_test ~ty_super:ty_scrut ~ctxt
     with
     | Subtyping.Answer.No _err ->
       (* The test type is not a subtype of the scrutinee so the refinement is to 
         nothing. The complement of the refinement is just the original
         scrutinee type : if T </: S,  S & T = nothing , S - T = T. 
         - *)
       let rfmt = Ty.Refinement.disjoint prov, None in
       (* and _rtmt_cmpl = Ty.Refinement.replace_with ty_scrut, None in *)
       rfmt
       (* , rfmt_cmpl *)
     | Subtyping.Answer.Yes ->
       (* The test type is a subtype of the scrutinee so the refinement is to
          exactly the test type i.e. it is _technically_ redunant to apply an
          intersection. We do still generate this as the refinement since we
          need to keep track of the supertype in some cases for exposure to
          work correctly. The complement of the refinement is the difference
          of the scrutinee and the test types:
          if T <: S, T & S = T, S - T == S & ~T
       *)
       let rfmt = Ty.Refinement.intersect_with prov ty_test, None in
       (* and _rfmt_cmpl = Ty.Refinement.disjoint prov, None in *)
       rfmt
       (* , rfmt_cmpl *)
     | Subtyping.Answer.Maybe ->
       (* The test type might be a subtype. The complement is the difference
          between the scrutinee and test type *)
       Ty.Refinement.intersect_with prov ty_test, None)

(* ~~ Refine top-level generics ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and refine_top_level_generic_test ty_scrut prov_test name_test ~ctxt =
  let ty_scrut, prov_test, name_test, ctxt =
    Eff.log_enter_top_level_generic_test ty_scrut prov_test name_test ctxt
  in
  (* If we have a generic in test position we need the scrutinee to be a subtype
     of its upperbound and a supertype of its lowerbound, otherwise it is disjoint *)
  let prov =
    Reporting.Prov.refine ~prov_scrut:(Ty.prov_of ty_scrut) ~prov_test
  in
  let Ty.Param_bounds.{ lower; upper } =
    Option.value_exn @@ Ctxt.Cont.ty_param_bounds ctxt name_test
  in
  Eff.log_exit_top_level_generic_test
  @@
  match
    Subtyping.Ask.(
      ( is_subtype ~ty_sub:lower ~ty_super:ty_scrut ~ctxt
      , is_subtype ~ty_sub:ty_scrut ~ty_super:upper ~ctxt ))
  with
  | Subtyping.Answer.No _, _ | _, Subtyping.Answer.No _ ->
    Ty.Refinement.disjoint prov, None
  | _ ->
    let ty_test = Ty.generic prov_test name_test in
    Ty.Refinement.intersect_with prov ty_test, None

and refine_top_level_generic_scrut prov_scrut name_scrut ty_test ~ctxt =
  let prov_scrut, name_scrut, ty_test, ctxt =
    Eff.log_enter_top_level_generic_scrut prov_scrut name_scrut ty_test ctxt
  in
  let prov =
    Reporting.Prov.refine ~prov_scrut ~prov_test:(Ty.prov_of ty_test)
  in
  let Ty.Param_bounds.{ upper; _ } =
    Option.value_exn @@ Ctxt.Cont.ty_param_bounds ctxt name_scrut
  in
  let ty_rfmt, ty_param_rfmt_opt = refine_ty ~ty_scrut:upper ~ty_test ~ctxt in
  Eff.log_exit_top_level_generic_scrut
  @@
  match name_scrut with
  (* ~~ this in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  (* If the scrutinee has type [this] then we generate a refinement because
     there is only one thing with type [this]. As well as the refinements
     resulting from refining the upper bound, we need to add the test type
     as an upper bound *)
  | Name.Ty_param.This ->
    let ty_scrut = Ty.this prov in
    let this_rfmt =
      Ctxt.Ty_param.Refinement.singleton Name.Ty_param.this
      @@ Ty.Param_bounds.create ~upper:ty_test ~lower:(Ty.nothing prov) ()
    in
    let rfmt =
      Option.value_map
        ty_param_rfmt_opt
        ~default:this_rfmt
        ~f:(fun (prov, other_rfmts) ->
          Ctxt.Ty_param.Refinement.meet this_rfmt other_rfmts ~prov)
    in
    (* TODO(mjt) we don't actually refine the type in this case but it seems
       overkill to make the refinement optional so we just intersect with
       itself for now *)
    Ty.Refinement.intersect_with prov ty_scrut, Some (prov, rfmt)
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
  | _ -> ty_rfmt, None
(* ~~ Refine existentials ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

and refine_existential_scrut prov_scrut exists_scrut ty_test ~ctxt =
  let prov_scrut, Ty.Exists.{ quants; body }, ty_test, ctxt =
    Eff.log_enter_existential_scrut prov_scrut exists_scrut ty_test ctxt
  in
  let prov =
    let prov_test = Ty.prov_of ty_test in
    Prov.refine ~prov_test ~prov_scrut
  in
  (* Unpack, bind and subsitute fresh names for the quantifiers in the body of
     the scrutinee type
     [subst] maps from the declared type parameter name to the the fresh name
     [quants] is the list of quantifiers using the fresh names*)
  let subst, quants =
    let generics = Eff.request_fresh_ty_params (List.length quants) in
    let subst, quants =
      List.unzip
      @@ List.map2_exn
           quants
           generics
           ~f:
             (fun
               Ty.Param.{ name = Located.{ elem; span }; param_bounds }
               fresh_name
             ->
             ( (elem, Ty.generic Prov.empty fresh_name)
             , Ty.Param.
                 { name = Located.{ elem = fresh_name; span }; param_bounds } ))
    in
    let subst = Name.Ty_param.Map.of_alist_exn subst in
    subst, quants
  in
  (* Apply the substitution to the body so that is mentions the new names which
     are fresh wrt to the enclosing context *)
  let body = Ty.apply_subst body ~subst ~combine_prov:(fun p _ -> p) in
  (* Bind the quantifiers and refine the body against the test type *)
  let ty_rfmt, ty_param_rfmt_opt =
    let ctxt = Ctxt.Cont.bind_ty_params ctxt quants in
    refine_ty ~ty_scrut:body ~ty_test ~ctxt
  in
  (* If we have refined any type parameters corresponding
     to our quantfiers we need to apply them before doing this. We also need
     to remove those type parameters from the refinement since they don't
     exist in the outer scope *)
  let quants, ty_param_rfmt_opt =
    Option.value_map
      ty_param_rfmt_opt
      ~default:(quants, ty_param_rfmt_opt)
      ~f:(fun (prov_refn, refn) ->
        (* We have type parameter refinements so find the refinement we should
           apply to each quantifier *)
        let quants =
          List.map quants ~f:(fun Ty.Param.{ name; param_bounds } ->
            let param_bounds =
              match Ctxt.Ty_param.Refinement.find refn name.Located.elem with
              | Ctxt.Ty_param.Refinement.Bounds bounds_delta ->
                (* TODO(mjt): find an example where we haven't solved and figure out
                   if we actually do need to meet here *)
                Ty.Param_bounds.meet param_bounds bounds_delta ~prov
              | Ctxt.Ty_param.Refinement.Bounds_top -> param_bounds
              | Ctxt.Ty_param.Refinement.Bounds_bottom ->
                Ty.Param_bounds.bottom prov
            in
            Ty.Param.{ name; param_bounds })
        in
        (* Then unbind the quantifiers in the refinement *)
        let refn =
          Ctxt.Ty_param.Refinement.unbind_all refn
          @@ List.map quants ~f:(fun Ty.Param.{ name; _ } -> name.Located.elem)
        in
        quants, Some (prov_refn, refn))
  in
  (* Update the type refinement to re-pack the existential, using the possibly
     refined quantifiers *)
  let ty_rfmt =
    match ty_rfmt with
    | Ty.Refinement.Disjoint _ -> ty_rfmt
    | Ty.Refinement.Intersect_with (prov_body, body') ->
      (* If the refinement is the intersection with the scrutinee type, bring that
         inside the body - this is ok since they must share the same quantifiers *)
      let body = Ty.inter ~prov:prov_body [ body; body' ] in
      let ty_test = Ty.exists ~quants ~body prov in
      Ty.Refinement.replace_with ty_test
    | Ty.Refinement.Replace_with body ->
      let ty_test = Ty.exists ~quants ~body prov in
      Ty.Refinement.replace_with ty_test
  in
  Eff.log_exit_existential_scrut (ty_rfmt, ty_param_rfmt_opt)

and refine_existential_test ty_scrut prov_test exists_test ~ctxt =
  let ty_scrut, prov_test, Ty.Exists.{ quants; body }, ctxt =
    Eff.log_enter_existential_test ty_scrut prov_test exists_test ctxt
  in
  let prov =
    let prov_scrut = Ty.prov_of ty_scrut in
    Prov.refine ~prov_test ~prov_scrut
  in
  (* Unpack, bind and subsitute fresh names for the quantifiers in the body of
     the test type.
     [subst] maps from the declared type parameter name to the the fresh name
     [quants] is the list of quantifiers using the fresh names*)
  let generics = Eff.request_fresh_ty_params (List.length quants) in
  let subst, quants =
    let subst, quants =
      List.unzip
      @@ List.map2_exn
           quants
           generics
           ~f:
             (fun
               Ty.Param.{ name = Located.{ elem; span }; param_bounds }
               fresh_name
             ->
             ( (elem, Ty.generic Prov.empty fresh_name)
             , Ty.Param.
                 { name = Located.{ elem = fresh_name; span }; param_bounds } ))
    in
    let subst = Name.Ty_param.Map.of_alist_exn subst in
    subst, quants
  in
  let body = Ty.apply_subst body ~subst ~combine_prov:(fun p _ -> p) in
  (* Bind the quantifiers and refine the scrutinee against the body of the test type *)
  let ty_rfmt, ty_param_rfmt_opt =
    let ctxt = Ctxt.Cont.bind_ty_params ctxt quants in
    refine_ty ~ty_scrut ~ty_test:body ~ctxt
  in
  let quants, ty_param_rfmt_opt =
    Option.value_map
      ty_param_rfmt_opt
      ~default:(quants, None)
      ~f:(fun (prov_rfmt, refn) ->
        let quants =
          List.map quants ~f:(fun Ty.Param.{ name; param_bounds } ->
            let param_bounds =
              match Ctxt.Ty_param.Refinement.find refn name.Located.elem with
              | Ctxt.Ty_param.Refinement.Bounds bounds_delta ->
                (* TODO(mjt): find an example where we haven't solved and figure out if we actually do need to meet here *)
                Ty.Param_bounds.meet param_bounds bounds_delta ~prov
              | Ctxt.Ty_param.Refinement.Bounds_top -> param_bounds
              | Ctxt.Ty_param.Refinement.Bounds_bottom ->
                Ty.Param_bounds.bottom prov
            in
            Ty.Param.{ name; param_bounds })
        in
        (* 2) Unbind the quantifiers in the refinement *)
        let refn =
          Ctxt.Ty_param.Refinement.unbind_all refn
          @@ List.map quants ~f:(fun Ty.Param.{ name; _ } -> name.Located.elem)
        in
        quants, Some (prov_rfmt, refn))
  in
  (* Update the type refinement to re-pack the existential, using the possibly
     refined quantifiers *)
  let ty_rfmt =
    match ty_rfmt with
    | Ty.Refinement.Disjoint _ -> ty_rfmt
    | Ty.Refinement.Intersect_with (prov_body, body) ->
      (* If the refinement is the intersection with the scrutinee type, bring that
         inside the body - this is ok since they must share the same quantifiers *)
      let body = Ty.inter ~prov [ ty_scrut; body ] in
      let ty_test = Ty.exists ~quants ~body prov_body in
      Ty.Refinement.replace_with ty_test
    | Ty.Refinement.Replace_with body ->
      let ty_test = Ty.exists ~quants ~body prov in
      Ty.Refinement.replace_with ty_test
  in
  Eff.log_exit_existential_test (ty_rfmt, ty_param_rfmt_opt)

(* ~~ Refine union types in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Refining a union type means we can eliminate the elements which are not
    supertypes of the test type - refinement is an assertion that
    we have the test type in hand and this can only be true for the parts of
    the union which are supertypes. Once we find the refinements resulting
    from the 'good' elements, we find the meet to find what requirements
    are common to all *)
and refine_union_scrut prov ~ty_scruts ~ty_test ~ctxt =
  let prov, ty_scruts, ty_test, ctxt =
    Eff.log_enter_union_scrut prov ty_scruts ty_test ctxt
  in
  let refns =
    List.map ty_scruts ~f:(fun ty_scrut -> refine_ty ~ty_scrut ~ty_test ~ctxt)
  in
  let tys, refns =
    List.fold2_exn
      ty_scruts
      refns
      ~init:([], [])
      ~f:(fun (tys, refns) ty_scrut (rfmt, param_rfmt_opt) ->
        match rfmt with
        | Ty.Refinement.Disjoint _ -> tys, refns
        | _ ->
          ( Ty.refine ty_scrut ~rfmt :: tys
          , Option.value_map
              param_rfmt_opt
              ~default:refns
              ~f:(fun (_prov, refn) -> refn :: refns) ))
  in
  Eff.log_exit_union_scrut
  @@
  match tys with
  | [] -> Ty.Refinement.disjoint prov, None
  | _ ->
    ( Replace_with (Ty.union tys ~prov)
    , Some (prov, Ctxt.Ty_param.Refinement.join_many refns ~prov) )

(* ~~ Refine union types in test position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

and refine_union_test prov ~ty_tests ~ty_scrut ~ctxt =
  let ty_scrut, prov, ty_tests, ctxt =
    Eff.log_enter_union_test ty_scrut prov ty_tests ctxt
  in
  let res =
    sequence_any
    @@ List.map ty_tests ~f:(fun ty_test -> refine_ty ~ty_scrut ~ty_test ~ctxt)
  in
  Eff.log_exit_union_test
  @@
  match res with
  | Ok refns ->
    let tys, refns = combine_one ty_scrut refns in
    ( Replace_with (Ty.union tys ~prov)
    , Some (prov, Ctxt.Ty_param.Refinement.join_many refns ~prov) )
  | Error _provs -> Ty.Refinement.Disjoint prov, None

(* ~~ Refine intersection types in scrutinee position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Refining an intersection type doesn't let us elminate any element - they
    must all be supertypes of the test type - refinement is an assertion that
    we have the test type in hand so we must be able to view it at all of the
    types in the intersection *)
and refine_inter_scrut prov ~ty_scruts ~ty_test ~ctxt =
  let prov, ty_scruts, ty_test, ctxt =
    Eff.log_enter_inter_scrut prov ty_scruts ty_test ctxt
  in
  let res =
    sequence_all
    @@ List.map ty_scruts ~f:(fun ty_scrut ->
      refine_ty ~ty_scrut ~ty_test ~ctxt)
  in
  Eff.log_exit_inter_scrut
  @@
  match res with
  | Ok refns ->
    let tys, refns = combine ty_scruts refns in
    ( Replace_with (Ty.inter tys ~prov)
    , Some (prov, Ctxt.Ty_param.Refinement.meet_many refns ~prov) )
  | Error _provs -> Ty.Refinement.Disjoint prov, None

(* ~~ Refine intersection types in test position ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and refine_inter_test prov ~ty_tests ~ty_scrut ~ctxt =
  let ty_scrut, prov, ty_tests, ctxt =
    Eff.log_enter_inter_test ty_scrut prov ty_tests ctxt
  in
  let res =
    sequence_all
    @@ List.map ty_tests ~f:(fun ty_test -> refine_ty ~ty_scrut ~ty_test ~ctxt)
  in
  Eff.log_exit_inter_test
  @@
  match res with
  | Ok refns ->
    let tys, refns = combine_one ty_scrut refns in
    ( Replace_with (Ty.inter tys ~prov)
    , Some (prov, Ctxt.Ty_param.Refinement.meet_many refns ~prov) )
  | Error _provs -> Ty.Refinement.disjoint prov, None

(* ~~ Refine constructor types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and refine_ctor ~ctor_scrut ~ctor_test ~prov_scrut ~prov_test ~ctxt =
  let prov_scrut, ctor_scrut, prov_test, ctor_test, ctxt =
    Eff.log_enter_ctor prov_scrut ctor_scrut prov_test ctor_test ctxt
  in
  let prov = Reporting.Prov.refine ~prov_scrut ~prov_test in
  let Ty.Ctor.{ args = args_scrut; name = name_scrut } = ctor_scrut in
  Eff.log_exit_ctor
  @@
  match Eff.ask_up ~of_:ctor_test ~at:name_scrut with
  | Not_a_subclass ->
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
  | Direct args_up | Transitive args_up ->
    (* The test type is a subtype of the scrutinee type and we now have the type
       arguments for the test constructor seen at its instantiation at the
       scrutinee so we can refine each argument
    *)
    (* If the type argument from the scrutinee is not a generic but the type in
       the correponding arugment from the test is a generic we will need to know
       the declared variance of the parameter *)
    let variance =
      Option.value_exn (Eff.ask_ty_param_variances ctor_scrut.name)
    in
    (* We need *)
    let res =
      sequence_all
      @@ List.map3_exn
           args_scrut
           args_up
           variance
           ~f:(fun ty_scrut ty_test variance ->
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
       (* ( Replace_with ty *)
       ( Intersect_with (prov, ty)
       , Some (prov, Ctxt.Ty_param.Refinement.meet_many refns ~prov:prov_test) )
     | Error _provs -> Ty.Refinement.disjoint prov, None)

and refine_ctor_arg ~ty_scrut ~ty_test variance ~ctxt =
  let ty_scrut, ty_test, variance, ctxt =
    Eff.log_enter_ctor_arg ty_scrut ty_test variance ctxt
  in
  let prov_scrut, node_scrut = Ty.prj ty_scrut
  and prov_test, node_test = Ty.prj ty_test in
  let prov = Reporting.Prov.refine ~prov_scrut ~prov_test in
  Eff.log_exit_ctor
  @@
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
            ; g_test, Option.value_exn (Ctxt.Cont.ty_param_bounds ctxt g_scrut)
            ] ) )
  | Ty.Node.Generic g_scrut, _, _ ->
    (* GADT case - we have a concrete type in test position so refine the bounds of the generic to this type *)
    ( Replace_with ty_test
    , Some
        ( prov
        , Ctxt.Ty_param.Refinement.singleton g_scrut
          @@ Ty.Param_bounds.create_equal ty_test ) )
  | _, Ty.Node.Generic g_test, Variance.Cov ->
    (* We have a concrete type in scrutinee position and a covariant generic in test position so we can refine it
       further by adding the concrete type as an upper bound *)
    ( Replace_with ty_test
    , Some
        ( prov
        , Ctxt.Ty_param.Refinement.singleton g_test
          @@ Ty.Param_bounds.create
               ~upper:ty_scrut
               ~lower:(Ty.nothing prov_scrut)
               () ) )
  | _, Ty.Node.Generic g_test, Variance.Contrav ->
    ( Replace_with ty_test
    , Some
        ( prov
        , Ctxt.Ty_param.Refinement.singleton g_test
          @@ Ty.Param_bounds.create
               ~lower:ty_scrut
               ~upper:(Ty.mixed prov_scrut)
               () ) )
  | _, Ty.Node.Generic g_test, Variance.Inv ->
    ( Replace_with ty_test
    , Some
        ( prov
        , Ctxt.Ty_param.Refinement.singleton g_test
          @@ Ty.Param_bounds.create_equal ty_scrut ) )
    (* We have two concrete types so we need to recurse into them to discover refinements on any nested generic *)
  | _, _, Variance.Cov -> refine_ty ~ty_scrut ~ty_test ~ctxt
  | _, _, Variance.Contrav ->
    refine_ty ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt
  | _, _, Variance.Inv ->
    let res =
      sequence_all
        [ refine_ty ~ty_scrut ~ty_test ~ctxt
        ; refine_ty ~ty_scrut:ty_test ~ty_test:ty_scrut ~ctxt
        ]
    in
    (match res with
     | Ok refns ->
       let tys, refns = combine [ ty_scrut; ty_scrut ] refns in
       ( Replace_with (Ty.inter tys ~prov)
       , Some (prov, Ctxt.Ty_param.Refinement.meet_many refns ~prov) )
     | Error _provs -> Ty.Refinement.disjoint prov, None)
;;
