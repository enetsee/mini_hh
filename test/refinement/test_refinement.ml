open Core
open Reporting
open Test_common

let ctor_nm nm = Name.Ctor.of_string nm
let mk_class nm ?(args = []) ?(extends = []) () = ctor_nm nm, args, extends
let ty_param_nm nm = Name.Ty_param.of_string nm
let mk_generic nm = ty_param_nm nm

let program_of_string prog_str =
  Result.ok_or_failwith @@ Result.map_error ~f:Source.Parse.Err.show @@ Source.Parse.parse_string prog_str
;;

let result =
  Alcotest.result
    (Alcotest.pair Testable.refinement @@ Alcotest.option @@ Alcotest.pair Testable.prov Testable.ty_param_refine)
    Testable.subtyping_err
;;

module Gadt_covariant = struct
  let agreement =
    let prog_str = {|class Four {}
interface I<+T> {}
class A implements I<Four> {}
|} in
    let prog = program_of_string prog_str in
    let oracle, errs = Oracle.of_program Oracle.empty prog in
    assert (List.is_empty errs);
    (* Scrutinee and test type *)
    let ta = ty_param_nm "Ta" in
    let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty ta ]
    and ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[] in
    (* Set up context *)
    let ty_param = Ctxt.Ty_param.(bind empty ta @@ Ty.Param_bounds.top Prov.empty) in
    let cont_ctxt = Ctxt.Cont.{ empty with ty_param } in
    let comp = Refinement.refine ~ty_scrut ~ty_test ~ctxt:cont_ctxt in
    let actual = fst @@ Refinement.Eff.run comp 0 oracle in
    (* let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in *)
    (* Expected type parameter refinement *)
    let expect =
      let four = Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] in
      let prov_scrut = Ty.prov_of ty_scrut
      and prov_test = Ty.prov_of ty_test in
      let prov = Prov.refine ~prov_scrut ~prov_test in
      Ok
        ( Ty.Refinement.Replace_with ty_test
        , Some (prov, Ctxt.Ty_param.Refinement.(singleton ta @@ Ty.Param_bounds.create ~lower:four ~upper:four ())) )
    in
    let test () = Alcotest.check result prog_str actual expect in
    Alcotest.test_case "gadt refinement with agreement between bounds" `Quick test
  ;;

  let test_cases = [ agreement ]
end

let test_cases = List.concat [ Gadt_covariant.test_cases ]

(* let result = Alcotest.result Testable.refinement Testable.subtyping_err let ctor_nm nm = Name.Ctor.of_string nm let
   mk_class nm ?(args = []) ?(extends = []) () = ctor_nm nm, args, extends let ty_param_nm nm = Name.Ty_param.of_string
   nm let mk_generic nm = ty_param_nm nm

   let class_chain = [ mk_class "Seven" () ; mk_class "Six" ~extends:[ ctor_nm "Seven", [] ] () ; mk_class "Five"
   ~extends:[ ctor_nm "Six", [] ] () ; mk_class "Four" ~extends:[ ctor_nm "Five", [] ] () ; mk_class "Three" ~extends:[
   ctor_nm "Four", [] ] () ; mk_class "Two" ~extends:[ ctor_nm "Three", [] ] () ; mk_class "One" ~extends:[ ctor_nm
   "Two", [] ] () ] ;;

   module Gadt_covariant = struct let oracle = Oracle.( add_classishes_exn empty (class_chain @ [ mk_class "I" ~args:[
   Name.Ty_param.of_string "T", Variance.cov, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "A" ~extends:[
   ctor_nm "I", [ Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] ] ] () ])) ;;

   let agreement = (* Scrutinee and test type *) let ta = ty_param_nm "Ta" in let ty_scrut = Ty.ctor Prov.empty
   ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty ta ] and ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[]
   in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty ta @@ Ty.Param_bounds.top Prov.empty) in let
   ty_param_refine = Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle
   () in (* Expected type parameter refinement *) let expect = let four = Ty.ctor Prov.empty ~name:(ctor_nm "Four")
   ~args:[] in Ok (Refinement.replace_with ty_test Envir.Ty_param_refine.(singleton ta @@ Ty.Param_bounds.create
   ~lower:four ~upper:four ())) in let test () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four>
   {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in
   Alcotest.test_case "gadt refinement with agreement between bounds" `Quick test ;;

   let disagreement = (* Scrutinee and test type *) let ta = Name.Ty_param.Ty_param "Ta" in let ty_scrut = Ty.ctor
   Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty ta ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm
   "A") ~args:[] in (* Set up context *) let three = Ty.ctor Prov.empty ~name:(ctor_nm "Three") ~args:[] and four =
   Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] in let ta_bounds = Ty.Param_bounds.create ~lower:(Ty.nothing
   Prov.empty) ~upper:three () in let ty_param = Envir.Ty_param.(bind empty ta ta_bounds) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected
   type parameter refinement *) let expect = Ok (Refinement.replace_with ty_test Envir.Ty_param_refine.( singleton ta @@
   Ty.Param_bounds.create ~lower:four ~upper:(Ty.inter ~prov:Prov.empty [ four ]) ())) in let test () = Alcotest.check
   result "\ninterface I<T>\nclass A implements I<int> {}\nI<Ta> ↓ A = { One | Four <= Ta <= Four }\n"
   (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "gadt refinement with agreement between
   bounds" `Quick test ;;

   let test_cases = [ agreement; disagreement ] end

   module Invariant_class_impl_covariant = struct let oracle = Oracle.( add_classishes_exn empty ([ mk_class "ICo"
   ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "MyClass" ~args: [ (
   mk_generic "T" , Variance.Inv , Ty.Param_bounds.create ~lower:(Ty.ctor Prov.empty ~name:(ctor_nm "Two") ~args:[])
   ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "Six") ~args:[]) () , Span.empty ) ] ~extends:[ ctor_nm "ICo", [ Ty.generic
   Prov.empty @@ ty_param_nm "T" ] ] () ] @ class_chain)) ;;

   (* ; mk_class "CConcreteImplICo" ~extends:[ ctor_nm "ICo", [ Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] ] ]
   () ; mk_class "CImplIContra" ~args: [ ( mk_generic "T" , Variance.Inv , Ty.Param_bounds.create ~lower:(Ty.ctor
   Prov.empty ~name:(ctor_nm "Two") ~args:[]) ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "Six") ~args:[]) () ) ]
   ~extends:[ ctor_nm "IContra", [ Ty.generic @@ ty_param_nm "T" ] ] () ; mk_class "CImplIInv" ~args: [ ( mk_generic "T"
   , Variance.Inv , Ty.Param_bounds.create ~lower:(Ty.ctor Prov.empty ~name:(ctor_nm "Two") ~args:[]) ~upper:(Ty.ctor
   Prov.empty ~name:(ctor_nm "Six") ~args:[]) () ) ] ~extends:[ ctor_nm "IInv", [ Ty.generic @@ ty_param_nm "T" ] ] ()
   ]) *)

   let doc_case_1 = (* Scrutinee and test types *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICo") ~args:[
   Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "MyClass")
   ~args:[ Ty.generic Prov.empty @@ ty_param_nm "Ta" ] in (* Set up context *) let ta = Name.Ty_param.of_string "Ta" in
   let ty_param = Envir.Ty_param.( bind empty ta @@ Ty.Param_bounds.create ~lower:(Ty.ctor Prov.empty ~name:(ctor_nm
   "Two") ~args:[]) ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "Six") ~args:[]) ()) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected
   type parameter refinements *) let expect = Ok Refinement.( replace_with ty_test @@ Envir.Ty_param_refine.singleton ta
   @@ Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty) ~upper:Ty.(ctor Prov.empty ~name:(ctor_nm "Four") ~args:[])
   ()) in let test () = Alcotest.check result "\n\ interface ICo<+T>\n\ class MyClass<T super Two as Six> extends ICo<T>
   {}\n\ Γ, Two <= Ta <= Six ⊢ ICo<Four> ↓ CImplCo<Ta> = {Ta <= Four}\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
   expect in Alcotest.test_case "inv impl cov / case 1" `Quick test ;;

   let doc_case_2 = (* Scrutinee and test types *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICo") ~args:[
   Ty.ctor Prov.empty ~name:(ctor_nm "One") ~args:[] ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "MyClass")
   ~args:Ty.[ generic Prov.empty @@ ty_param_nm "Ta" ] in (* Set up context *) let ta = Name.Ty_param.Ty_param "Ta" in
   let ty_param = Envir.Ty_param.( bind empty ta @@ Ty.Param_bounds.create ~lower:(Ty.ctor Prov.empty ~name:(ctor_nm
   "Two") ~args:[]) ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "Six") ~args:[]) ()) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected
   type parameter refinements *) let bounds_expect = Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty)
   ~upper:Ty.(ctor Prov.empty ~name:(ctor_nm "One") ~args:[]) () in let expect = Ok (Refinement.replace_with ty_test
   Envir.Ty_param_refine.(singleton ta bounds_expect)) in let test () = Alcotest.check result "\n\ interface ICo<+T>\n\
   class MyClass<T super Two as Six> extends ICo<T> {}\n\ Γ, Two <= Ta <= Six ⊢ ICo<One> ↓ CImplCo<Ta> = {Ta <= One}\n"
   (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "inv impl cov / case 2" `Quick test ;;

   let doc_case_3 = (* Scrutinee and test types *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICo") ~args:Ty.[
   ctor Prov.empty ~name:(ctor_nm "Seven") ~args:[] ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "MyClass")
   ~args:Ty.[ generic Prov.empty @@ ty_param_nm "Ta" ] in (* Set up context *) let ta = Name.Ty_param.Ty_param "Ta" in
   let ty_param = Envir.Ty_param.( bind empty ta @@ Ty.Param_bounds.create ~lower:(Ty.ctor Prov.empty ~name:(ctor_nm
   "Two") ~args:[]) ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "Six") ~args:[]) ()) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected
   type parameter refinements *) let bounds_expect = Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty)
   ~upper:Ty.(ctor Prov.empty ~name:(ctor_nm "Seven") ~args:[]) () in let expect = Ok (Refinement.replace_with ty_test
   Envir.Ty_param_refine.(singleton ta bounds_expect)) in let test () = Alcotest.check result "\n\ interface ICo<+T>\n\
   class MyClass<T super Two as Six> extends ICo<T> {}\n\ Γ, Two <= Ta <= Six ⊢ ICo<Seven> ↓ CImplCo<Ta> = {Ta <=
   Seven}\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "inv impl cov / case 3" `Quick
   test ;;

   let doc_case_4 = let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICo") ~args:Ty.[ generic Prov.empty @@ ty_param_nm
   "Tco" ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "MyClass") ~args:Ty.[ generic Prov.empty @@ ty_param_nm
   "Ta" ] in let ta = mk_generic "Ta" and tco = mk_generic "Tco" in let ta_bounds = Ty.Param_bounds.create
   ~lower:(Ty.ctor Prov.empty ~name:(ctor_nm "Two") ~args:[]) ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "Six") ~args:[])
   () and tco_bounds = Ty.Param_bounds.create ~lower:(Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[])
   ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "Six") ~args:[]) () in let ty_param = Envir.Ty_param.(bind (bind empty ta
   ta_bounds) tco tco_bounds) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create
   ~ty_param ~ty_param_refine ~oracle () in let tco_bounds_expect = ta_bounds in let ta_bounds_expect =
   Ty.Param_bounds.create_equal Ty.(generic Prov.empty @@ ty_param_nm "Tco") in let expect = Ok Refinement.(
   replace_with ty_test @@ Envir.Ty_param_refine.bounds @@ Name.Ty_param.Map.of_alist_exn [ ta, ta_bounds_expect; tco,
   tco_bounds_expect ]) in let test () = Alcotest.check result "\n\ interface ICo<+T>\n\ class MyClass<T super Two as
   Six> extends ICo<T> {}\n\ Γ, Two <= Ta <= Six, Four <= Tco <= Six ⊢ ICo<Tco> ↓ CImplCo<Ta> = {Ta <= Seven}\n"
   (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "inv impl cov / case 4" `Quick test ;;

   let test_cases = [ doc_case_1; doc_case_2; doc_case_3; doc_case_4 ] end

   module Non_generic_class_impl_covariant = struct let oracle = Oracle.( add_classishes_exn empty [ mk_class "Seven" ()
   ; mk_class "Six" ~extends:[ ctor_nm "Seven", [] ] () ; mk_class "Five" ~extends:[ ctor_nm "Six", [] ] () ; mk_class
   "Four" ~extends:[ ctor_nm "Five", [] ] () ; mk_class "Three" ~extends:[ ctor_nm "Four", [] ] () ; mk_class "Two"
   ~extends:[ ctor_nm "Three", [] ] () ; mk_class "One" ~extends:[ ctor_nm "Two", [] ] () ; mk_class "ICo" ~args:[
   mk_generic "T", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "MyClass" ~extends:[ ctor_nm
   "ICo", [ Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] ] ] () ]) ;;

   let doc_case_1 = (* Scrutinee and test types *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICo") ~args:Ty.[
   ctor Prov.empty ~name:(ctor_nm "Two") ~args:[] ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "MyClass")
   ~args:[] in (* Set up refinement context *) let ty_param = Envir.Ty_param.empty in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Even
   though Four is not a subtype of Two we have to allow for the possibility that both Two and Four are supertypes of
   some third type so they have a non-empty intersection. *) let expect = Ok (Refinement.replace_with ty_test
   Envir.Ty_param_refine.empty) in let test () = Alcotest.check result "\ninterface ICo<+T>\nclass MyClass extends
   ICo<Four> {}\nICo<Two> ↓ MyClass = err\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case
   "non-generic class impl covariant / case 1" `Quick test ;;

   let doc_case_2 = (* Scrutinee and test types *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICo") ~args:Ty.[
   ctor Prov.empty ~name:(ctor_nm "Six") ~args:[] ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "MyClass")
   ~args:[] in (* Set up refinement context *) let ty_param = Envir.Ty_param.empty in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expect
   no type parameter refinement *) let expect = Ok (Refinement.replace_with ty_test Envir.Ty_param_refine.top) in let
   test () = Alcotest.check result "\ninterface ICo<+T>\nclass MyClass extends ICo<Four> {}\nICo<Two> ↓ MyClass = {}\n"
   (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "non-generic class impl covariant / case 2"
   `Quick test ;;

   let test_cases = [ doc_case_1; doc_case_2 ] end

   module Nested = struct let akenn1 = (* class B<Tb> {} class A<Ta> {} class C {} class D extends A<B<C>> {} *) let
   oracle = Oracle.( add_classishes_exn empty [ mk_class "B" ~args:[ mk_generic "Tb", Variance.Inv, Ty.Param_bounds.top
   Prov.empty, Span.empty ] () ; mk_class "A" ~args:[ mk_generic "Ta", Variance.Inv, Ty.Param_bounds.top Prov.empty,
   Span.empty ] () ; mk_class "C" () ; mk_class "D" ~extends: [ ( ctor_nm "A" , [ Ty.ctor Prov.empty ~name:(ctor_nm "B")
   ~args:[ Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[] ] ] ) ] () ]) in (* Scrutinee and test type *) let tab =
   Name.Ty_param.Ty_param "Tab" in let ty_scrut = let b = Ty.ctor Prov.empty ~name:(ctor_nm "B") ~args:[ Ty.generic
   Prov.empty tab ] in Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[ b ] in let ty_test = Ty.ctor Prov.empty
   ~name:(ctor_nm "D") ~args:[] in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty tab @@
   Ty.Param_bounds.top Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt =
   Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected type parameter refinement *) let expect =
   let c = Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[] in let bnds = Ty.Param_bounds.create ~lower:(Ty.union [ c; c
   ] ~prov:Prov.(refines ~prov_scrut:empty ~prov_test:empty)) ~upper:(Ty.inter [ c; c ] ~prov:Prov.(refines
   ~prov_scrut:empty ~prov_test:empty)) () in Ok (Refinement.replace_with ty_test Envir.Ty_param_refine.(singleton tab
   bnds)) in let test () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing
   <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement / nested /
   nested case" `Quick test ;;

   let akenn2 = (* class B<Tb> {} class A<-Ta> {}

   class C {}

   class D extends A<B<C>> {} class E<Te> extends B<Te>

   A<E<Tab>> ~~> D *) let oracle = Oracle.( add_classishes_exn empty [ mk_class "B" ~args:[ mk_generic "Tb",
   Variance.Inv, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "A" ~args:[ mk_generic "Ta",
   Variance.Contrav, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "C" () ; mk_class "D" ~extends: [ (
   ctor_nm "A" , [ Ty.ctor Prov.empty ~name:(ctor_nm "B") ~args:[ Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[] ] ] )
   ] () ; mk_class "E" ~args:[ mk_generic "Te", Variance.Inv, Ty.Param_bounds.top Prov.empty, Span.empty ] ~extends:[
   ctor_nm "B", [ Ty.generic Prov.empty (mk_generic "Te") ] ] () ]) in (* Scrutinee and test type *) let tae =
   Name.Ty_param.Ty_param "Tae" in let ty_scrut = let b = Ty.ctor Prov.empty ~name:(ctor_nm "E") ~args:[ Ty.generic
   Prov.empty tae ] in Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[ b ] in let ty_test = Ty.ctor Prov.empty
   ~name:(ctor_nm "D") ~args:[] in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty tae @@
   Ty.Param_bounds.top Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt =
   Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected type parameter refinement *) let expect =
   let c = Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[] in Ok Refinement.( replace_with ty_test
   Envir.Ty_param_refine.(singleton tae @@ Ty.Param_bounds.create ~lower:c ~upper:c ())) in let test () = Alcotest.check
   result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n" (Refinement.refine
   ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement / nested / nested case 2" `Quick test ;;

   let akenn3 = (* class B<Tb> {} class A<+Ta> {} class C {} class D extends A<B<C>> {} *) let oracle = Oracle.(
   add_classishes_exn empty [ mk_class "B" ~args:[ mk_generic "Tb", Variance.Inv, Ty.Param_bounds.top Prov.empty,
   Span.empty ] () ; mk_class "A" ~args:[ mk_generic "Ta", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] ()
   ; mk_class "C" () ; mk_class "D" ~extends: [ ( ctor_nm "A" , [ Ty.ctor Prov.empty ~name:(ctor_nm "B") ~args:[ Ty.ctor
   Prov.empty ~name:(ctor_nm "C") ~args:[] ] ] ) ] () ]) in (* Scrutinee and test type *) let tab =
   Name.Ty_param.Ty_param "Tab" in let ty_scrut = let b = Ty.ctor Prov.empty ~name:(ctor_nm "B") ~args:[ Ty.generic
   Prov.empty tab ] in Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[ b ] in let ty_test = Ty.ctor Prov.empty
   ~name:(ctor_nm "D") ~args:[] in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty tab @@
   Ty.Param_bounds.top Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt =
   Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected type parameter refinement *) let expect =
   let c = Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[] in let bnds = Ty.Param_bounds.create ~lower:c ~upper:c () in
   Ok (Refinement.replace_with ty_test Envir.Ty_param_refine.(singleton tab bnds)) in let test () = Alcotest.check
   result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n" (Refinement.refine
   ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement / nested / nested case 3" `Quick test ;;

   (** class Inv<T> {} class SubInv<T> extends Inv<T> {} class Contrav<-T> {} class SubContrav extends
   Contrav<Cov<Inv<End>>> {} class Cov<+T> {} class SubCov<+T> extends Cov<T> {} class End {}

   function refine<T>(Contrav<SubCov<SubInv<T>>> $scrut): void { if ($scrut is SubContrav) { expect<T>(new End()); } }
   *) let akenn4 = let oracle = Oracle.( add_classishes_exn empty [ mk_class "Inv" ~args:[ mk_generic "T", Variance.Inv,
   Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "SubInv" ~args:[ mk_generic "T", Variance.Inv,
   Ty.Param_bounds.top Prov.empty, Span.empty ] ~extends:[ ctor_nm "Inv", [ Ty.generic Prov.empty (ty_param_nm "T") ] ]
   () ; mk_class "Cov" ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class
   "SubCov" ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] ~extends:[ ctor_nm "Cov",
   [ Ty.generic Prov.empty (ty_param_nm "T") ] ] () ; mk_class "End" () ; mk_class "Contrav" ~args:[ mk_generic "T",
   Variance.Contrav, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "SubContrav" ~extends: [ ( ctor_nm
   "Contrav" , Ty. [ ctor Prov.empty ~name:(ctor_nm "Cov") ~args: [ ctor Prov.empty ~name:(ctor_nm "Inv") ~args:[ ctor
   Prov.empty ~name:(ctor_nm "End") ~args:[] ] ] ] ) ] () ]) in (* Scrutinee and test type *) let t_scrut =
   Name.Ty_param.Ty_param "Tscrut" in let ty_scrut = Ty.( ctor Prov.empty ~name:(ctor_nm "Contrav") ~args: [ ctor
   Prov.empty ~name:(ctor_nm "SubCov") ~args:[ ctor Prov.empty ~name:(ctor_nm "SubInv") ~args:[ generic Prov.empty
   t_scrut ] ] ]) in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "SubContrav") ~args:[] in (* Set up context *) let
   ty_param = Envir.Ty_param.(bind empty t_scrut @@ Ty.Param_bounds.top Prov.empty) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected
   type parameter refinement *) let expect = let c = Ty.ctor Prov.empty ~name:(ctor_nm "End") ~args:[] in let bnds =
   Ty.Param_bounds.create ~lower:c ~upper:c () in Ok (Refinement.replace_with ty_test Envir.Ty_param_refine.(singleton
   t_scrut bnds)) in let test () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = {
   nothing <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement /
   nested / nested case 4" `Quick test ;;

   let test_cases = [ akenn1; akenn2; akenn3; akenn4 ] end

   module Union_scrut = struct (* interface I<T> {} interface J<T> {} interface K {} class E implements I<Four>,
   J<Five>, K {}

   (I<T> | J<T>) is E

   Should let us refine T to int

   But,

   (I<T> | K) is E

   shouldn't let us refine T *)

   let oracle = Oracle.( add_classishes_exn empty (class_chain @ [ ( Name.Ctor.Ctor "I" , [ Name.Ty_param.Ty_param "T",
   Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ] , [] ) ; ( Name.Ctor.Ctor "J" , [ Name.Ty_param.Ty_param
   "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ] , [] ) ; Name.Ctor.Ctor "K", [], [] ; (
   Name.Ctor.Ctor "E" , [] , [ ctor_nm "I", [ Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] ] ; ctor_nm "J", [
   Ty.ctor Prov.empty ~name:(ctor_nm "Five") ~args:[] ] ; ctor_nm "K", [] ] ) ; Name.Ctor.Ctor "F", [], [ ctor_nm "I", [
   Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] ] ] ])) ;;

   let case_1 = (* Scrutinee and test type *) let t_scrut = Name.Ty_param.Ty_param "Tscrut" in let ty_scrut = let i =
   Ty.ctor Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty t_scrut ] in let j = Ty.ctor Prov.empty
   ~name:(ctor_nm "J") ~args:[ Ty.generic Prov.empty t_scrut ] in Ty.union [ i; j ] ~prov:Prov.empty in let ty_test =
   Ty.ctor Prov.empty ~name:(ctor_nm "E") ~args:[] in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty
   t_scrut @@ Ty.Param_bounds.top Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt =
   Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected type parameter refinement *) let expect =
   let four = Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] in let five = Ty.ctor Prov.empty ~name:(ctor_nm "Five")
   ~args:[] in let bnds = Ty.Param_bounds.create ~lower:(Ty.union [ five; four ] ~prov:Prov.empty) ~upper:(Ty.inter [
   five; four ] ~prov:Prov.empty) () in Ok (Refinement.replace_with Ty.(union [ ty_test; ty_test ] ~prov:Prov.empty)
   Envir.Ty_param_refine.(singleton t_scrut bnds)) in let test () = Alcotest.check result "\ninterface I<T>\nclass A
   implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect
   in Alcotest.test_case "union scrut 1" `Quick test ;;

   let case_2 = (* Scrutinee and test type *) let t_scrut = Name.Ty_param.Ty_param "Tscrut" in let ty_scrut = let i =
   Ty.ctor Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty t_scrut ] in let k = Ty.ctor Prov.empty
   ~name:(ctor_nm "K") ~args:[] in Ty.union [ i; k ] ~prov:Prov.empty in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm
   "E") ~args:[] in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty t_scrut @@ Ty.Param_bounds.top
   Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param
   ~ty_param_refine ~oracle () in (* Expected type parameter refinement *) let expect = let lower = Ty.ctor Prov.empty
   ~name:(ctor_nm "Four") ~args:[] in let upper = lower in Ok (Refinement.replace_with Ty.(union [ ty_test; ty_test ]
   ~prov:Prov.empty) @@ Envir.Ty_param_refine.singleton t_scrut @@ Ty.Param_bounds.create ~upper ~lower ()) in let test
   () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
   (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "union scrut 2" `Quick test ;;

   let case_3 = (* Scrutinee and test type *) let t_scrut = Name.Ty_param.Ty_param "Tscrut" in let ty_i = Ty.ctor
   Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty t_scrut ] in let ty_j = Ty.ctor Prov.empty
   ~name:(ctor_nm "J") ~args:[ Ty.generic Prov.empty t_scrut ] in let ty_scrut = Ty.union [ ty_i; ty_j ]
   ~prov:Prov.empty in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "F") ~args:[] in (* Set up context *) let
   ty_param = Envir.Ty_param.(bind empty t_scrut @@ Ty.Param_bounds.top Prov.empty) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected
   type parameter refinement *) let expect = let lower = Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] in let upper
   = lower in Ok (Refinement.replace_with Ty.( union [ inter [ ty_j; ty_test ] ~prov:Prov.(refines ~prov_scrut:empty
   ~prov_test:empty); ty_test ] ~prov:Prov.empty) (Envir.Ty_param_refine.singleton t_scrut @@ Ty.Param_bounds.create
   ~upper ~lower ())) in let test () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A
   = { nothing <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "union scrut
   3" `Quick test ;;

   let test_cases = [ case_1; case_2; case_3 ] end

   module Union_test = struct (* class Expr<T> class NumExpr extends Expr<Num> class ArraykeyExpr extends Expr<Arraykey>

   Expr<T> ~~> (NumExpr | ArraykeyExpr) === Expr<T> ~~> NumExpr OR Expr<T> ~~> ArraykeyExpr (Num & Arraykey) <= T <=
   (Num | Arraykey) *) let case_1 = (* Set up context *) let oracle = Oracle.( add_classishes_exn empty [ mk_class
   "Expr" ~args:[ ty_param_nm "T", Variance.Inv, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "NumExpr"
   ~extends:[ ctor_nm "Expr", [ Ty.num Prov.empty ] ] () ; mk_class "ArraykeyExpr" ~extends:[ ctor_nm "Expr", [
   Ty.arraykey Prov.empty ] ] () ]) in let t_scrut = ty_param_nm "Tscrut" in let ty_param = Envir.Ty_param.(bind empty
   t_scrut @@ Ty.Param_bounds.top Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt =
   Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* scrutinee & test types *) let ty_scrut = Ty.ctor
   Prov.empty ~name:(ctor_nm "Expr") ~args:[ Ty.generic Prov.empty t_scrut ] and ty_num_expr = Ty.ctor Prov.empty
   ~name:(ctor_nm "NumExpr") ~args:[] and ty_arraykey_expr = Ty.ctor Prov.empty ~name:(ctor_nm "ArraykeyExpr") ~args:[]
   in let ty_test = Ty.union ~prov:Prov.empty [ ty_arraykey_expr; ty_num_expr ] in (* expected result *) let expect =
   let ty = Ty.union ~prov:Prov.empty [ ty_num_expr; ty_arraykey_expr ] in let upper = Ty.union ~prov:Prov.empty [
   Ty.num Prov.empty; Ty.arraykey Prov.empty ] in let lower = Ty.inter ~prov:Prov.empty [ Ty.num Prov.empty; Ty.arraykey
   Prov.empty ] in let bnds = Ty.Param_bounds.create ~lower ~upper () in Ok (Refinement.replace_with ty
   Envir.Ty_param_refine.(singleton t_scrut bnds)) in let test () = Alcotest.check result "" (Refinement.refine
   ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "union test 1" `Quick test ;;

   let test_cases = [ case_1 ] end

   module Intersection_test = struct (* class Expr<T> class NumExpr extends Expr<Num> class ArraykeyExpr extends
   Expr<Arraykey>

   Expr<T> ~~> (NumExpr & ArraykeyExpr) (Num | Arraykey) <= T <= (Num & Arraykey) (Int | String | Float) <= T <= (Int)
   *) let case_1 = (* Set up context *) let oracle = Oracle.( add_classishes_exn empty [ mk_class "Expr" ~args:[
   ty_param_nm "T", Variance.Inv, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "NumExpr" ~extends:[
   ctor_nm "Expr", [ Ty.num Prov.empty ] ] () ; mk_class "ArraykeyExpr" ~extends:[ ctor_nm "Expr", [ Ty.arraykey
   Prov.empty ] ] () ]) in let t_scrut = ty_param_nm "Tscrut" in let ty_param = Envir.Ty_param.(bind empty t_scrut @@
   Ty.Param_bounds.top Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt =
   Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* scrutinee & test types *) let ty_scrut = Ty.ctor
   Prov.empty ~name:(ctor_nm "Expr") ~args:[ Ty.generic Prov.empty t_scrut ] and ty_num_expr = Ty.ctor Prov.empty
   ~name:(ctor_nm "NumExpr") ~args:[] and ty_arraykey_expr = Ty.ctor Prov.empty ~name:(ctor_nm "ArraykeyExpr") ~args:[]
   in let ty_test = Ty.inter ~prov:Prov.empty [ ty_arraykey_expr; ty_num_expr ] in (* expected result *) let expect =
   let ty = Ty.inter ~prov:Prov.empty [ ty_num_expr; ty_arraykey_expr ] in let upper = Ty.inter ~prov:Prov.empty [
   Ty.num Prov.empty; Ty.arraykey Prov.empty ] in let lower = Ty.union ~prov:Prov.empty [ Ty.num Prov.empty; Ty.arraykey
   Prov.empty ] in let bnds = Ty.Param_bounds.create ~lower ~upper () in Ok (Refinement.replace_with ty
   Envir.Ty_param_refine.(singleton t_scrut bnds)) in let test () = Alcotest.check result "" (Refinement.refine
   ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "intersection test 1" `Quick test ;;

   let test_cases = [ case_1 ] end

   module Intersection_scrut = struct let oracle = Oracle.( add_classishes_exn empty (class_chain @ [ ( Name.Ctor.Ctor
   "I" , [ Name.Ty_param.Ty_param "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ] , [] ) ;
   Name.Ctor.Ctor "K", [], [] ; ( Name.Ctor.Ctor "C" , [] , [ ctor_nm "I", [ Ty.ctor Prov.empty ~name:(ctor_nm "Four")
   ~args:[] ]; ctor_nm "K", [] ] ) ; Name.Ctor.Ctor "D", [], [ ctor_nm "I", [ Ty.ctor Prov.empty ~name:(ctor_nm "Four")
   ~args:[] ] ] ])) ;;

   let case_1 = (* Scrutinee and test type *) let t_scrut = Name.Ty_param.Ty_param "Tscrut" in let ty_scrut = let i =
   Ty.ctor Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty t_scrut ] in let k = Ty.ctor Prov.empty
   ~name:(ctor_nm "K") ~args:[] in Ty.inter [ i; k ] ~prov:Prov.empty in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm
   "C") ~args:[] in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty t_scrut @@ Ty.Param_bounds.top
   Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param
   ~ty_param_refine ~oracle () in (* Expected type parameter refinement *) let expect = let four = Ty.ctor Prov.empty
   ~name:(ctor_nm "Four") ~args:[] in let bnds = Ty.Param_bounds.create ~lower:four ~upper:four () in Ok
   (Refinement.replace_with Ty.(inter [ ty_test; ty_test ] ~prov:Prov.empty) Envir.Ty_param_refine.(singleton t_scrut
   bnds)) in let test () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing
   <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement /
   intersection case 1" `Quick test ;;

   let case_2 = (* Scrutinee and test type *) let t_scrut = Name.Ty_param.Ty_param "Tscrut" in let ty_i = Ty.ctor
   Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty t_scrut ] in let ty_k = Ty.ctor Prov.empty
   ~name:(ctor_nm "K") ~args:[] in let ty_scrut = Ty.inter [ ty_i; ty_k ] ~prov:Prov.empty in let ty_test = Ty.ctor
   Prov.empty ~name:(ctor_nm "D") ~args:[] in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty t_scrut @@
   Ty.Param_bounds.top Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt =
   Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected type parameter refinement *) let expect =
   let four = Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] in let bnds = Ty.Param_bounds.create ~lower:four
   ~upper:four () in Ok (Refinement.replace_with Ty.( inter [ inter [ ty_k; ty_test ] ~prov:Prov.(refines
   ~prov_scrut:empty ~prov_test:empty); ty_test ] ~prov:Prov.empty) Envir.Ty_param_refine.(singleton t_scrut bnds)) in
   let test () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <=
   Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement / intersection case
   2" `Quick test ;;

   let oracle = Oracle.( add_classishes_exn empty (class_chain @ [ ( Name.Ctor.Ctor "I" , [ Name.Ty_param.Ty_param "T",
   Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ] , [] ) ; ( Name.Ctor.Ctor "J" , [ Name.Ty_param.Ty_param
   "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ] , [] ) ; Name.Ctor.Ctor "K", [], [] ; (
   Name.Ctor.Ctor "E" , [] , [ ctor_nm "I", [ Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] ] ; ctor_nm "J", [
   Ty.ctor Prov.empty ~name:(ctor_nm "Five") ~args:[] ] ; ctor_nm "K", [] ] ) ])) ;;

   let case_3 = (* Scrutinee and test type *) let t_scrut = Name.Ty_param.Ty_param "Tscrut" in let ty_scrut = let i =
   Ty.ctor Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty t_scrut ] in let j = Ty.ctor Prov.empty
   ~name:(ctor_nm "J") ~args:[ Ty.generic Prov.empty t_scrut ] in Ty.inter [ i; j ] ~prov:Prov.empty in let ty_test =
   Ty.ctor Prov.empty ~name:(ctor_nm "E") ~args:[] in (* Set up context *) let ty_param = Envir.Ty_param.(bind empty
   t_scrut @@ Ty.Param_bounds.top Prov.empty) in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt =
   Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Expected type parameter refinement *) let expect =
   let four = Ty.ctor Prov.empty ~name:(ctor_nm "Four") ~args:[] in let five = Ty.ctor Prov.empty ~name:(ctor_nm "Five")
   ~args:[] in let bnds = Ty.Param_bounds.create ~lower:(Ty.inter [ five; four ] ~prov:Prov.empty) ~upper:(Ty.union [
   five; four ] ~prov:Prov.empty) () in Ok (Refinement.replace_with ty_test Envir.Ty_param_refine.(singleton t_scrut
   bnds)) in let test () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing
   <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement /
   intersection case 3" `Quick test ;;

   let test_cases = [ case_1; case_2 ] end

   module Existential_test = struct let case_1 = (* Set up context *) let oracle = Oracle.( add_classishes_exn empty [
   mk_class "ICo" ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class
   "MyClass" ~args: [ ( mk_generic "T" , Variance.Inv , Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty)
   ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[]) () , Span.empty ) ] ~extends:[ ctor_nm "ICo", [ Ty.generic
   Prov.empty @@ ty_param_nm "T" ] ] () ; mk_class "A" () ]) in let t_scrut = ty_param_nm "T" in let ty_param =
   Envir.Ty_param.(bind empty t_scrut @@ Ty.Param_bounds.top Prov.empty) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (*
   scrutinee & test types *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICo") ~args:[ Ty.generic Prov.empty
   t_scrut ] in let param_bounds_test = let lower = Ty.nothing Prov.empty and upper = Ty.ctor Prov.empty ~name:(ctor_nm
   "A") ~args:[] in Ty.Param_bounds.create ~lower ~upper () in let ty_test = let quants = [ Ty.Param.create
   ~name:(Located.create_empty @@ ty_param_nm "T") ~param_bounds:param_bounds_test () ] in let body = Ty.ctor Prov.empty
   ~name:(ctor_nm "MyClass") ~args:[ Ty.generic Prov.empty @@ ty_param_nm "T" ] in Ty.exists Prov.empty ~quants ~body in
   (* expected result *) let ty_expect = let lower = Ty.union ~prov:Prov.empty [ Ty.nothing Prov.empty; Ty.generic
   Prov.empty t_scrut ] in let upper = Ty.inter ~prov:Prov.empty [ Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[];
   Ty.generic Prov.empty t_scrut ] in let param_bounds = Ty.Param_bounds.create ~lower ~upper () in let quants = [
   Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm "T#1") ~param_bounds () ] in let body = Ty.ctor Prov.empty
   ~name:(ctor_nm "MyClass") ~args:[ Ty.generic Prov.empty @@ ty_param_nm "T#1" ] in Ty.exists Prov.empty ~quants ~body
   in let ty_param_refine_expect = Envir.Ty_param_refine.(singleton t_scrut param_bounds_test) in let expect = Ok
   (Refinement.replace_with ty_expect ty_param_refine_expect) in let test () = Alcotest.check result ""
   (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "existential as test, case 1" `Quick test
   ;;

   let case_2 = (* Set up context *) let oracle = Oracle.( add_classishes_exn empty [ mk_class "I" ~args:[ mk_generic
   "T", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "J" ~args: [ ( mk_generic "T" ,
   Variance.Inv , Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty) ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "A")
   ~args:[]) () , Span.empty ) ] () ; mk_class "A" () ]) in let t_scrut = ty_param_nm "T" in let ty_param =
   Envir.Ty_param.(bind empty t_scrut @@ Ty.Param_bounds.top Prov.empty) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (*
   scrutinee & test types *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty t_scrut
   ] in let param_bounds_test = let lower = Ty.nothing Prov.empty and upper = Ty.ctor Prov.empty ~name:(ctor_nm "A")
   ~args:[] in Ty.Param_bounds.create ~lower ~upper () in let ty_test = let quants = [ Ty.Param.create
   ~name:(Located.create_empty @@ ty_param_nm "T") ~param_bounds:param_bounds_test () ] in let body = Ty.ctor Prov.empty
   ~name:(ctor_nm "J") ~args:[ Ty.generic Prov.empty @@ ty_param_nm "T" ] in Ty.exists Prov.empty ~quants ~body in (*
   expected result *) let ty_expect = let quants = [ Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm "T#1")
   ~param_bounds:param_bounds_test () ] in let body = Ty.inter ~prov:Prov.(refines ~prov_scrut:Prov.empty
   ~prov_test:Prov.empty) [ ty_scrut; Ty.ctor Prov.empty ~name:(ctor_nm "J") ~args:[ Ty.generic Prov.empty @@
   ty_param_nm "T#1" ] ] in Ty.exists Prov.empty ~quants ~body in let ty_param_refine_expect = Envir.Ty_param_refine.top
   in let expect = Ok (Refinement.replace_with ty_expect ty_param_refine_expect) in let test () = Alcotest.check result
   "" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "existential as test, case 2" `Quick
   test ;;

   let test_cases = [ case_1; case_2 ] end

   module Existential_both = struct let case_1 = (* Set up context *) let oracle = Oracle.( add_classishes_exn empty [
   mk_class "ICo" ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class
   "MyClass" ~args: [ ( mk_generic "T" , Variance.Inv , Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty)
   ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[]) () , Span.empty ) ] ~extends:[ ctor_nm "ICo", [ Ty.generic
   Prov.empty @@ ty_param_nm "T" ] ] () ; mk_class "A" () ]) in let ty_param = Envir.Ty_param.empty in let
   ty_param_refine = Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle
   () in (* scrutinee & test types *) let t_scrut = ty_param_nm "T" in let param_bounds_scrut = Ty.Param_bounds.top
   Prov.empty in let ty_scrut = let quants = [ Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm "T")
   ~param_bounds:param_bounds_scrut () ] in let body = Ty.ctor Prov.empty ~name:(ctor_nm "ICo") ~args:[ Ty.generic
   Prov.empty t_scrut ] in Ty.exists Prov.empty ~quants ~body in let param_bounds_test = let lower = Ty.nothing
   Prov.empty and upper = Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[] in Ty.Param_bounds.create ~lower ~upper () in
   let ty_test = let quants = [ Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm "T")
   ~param_bounds:param_bounds_test () ] in let body = Ty.ctor Prov.empty ~name:(ctor_nm "MyClass") ~args:[ Ty.generic
   Prov.empty @@ ty_param_nm "T" ] in Ty.exists Prov.empty ~quants ~body in (* expected result *) let ty_expect = let
   body = let lower = Ty.union ~prov:Prov.empty [ Ty.nothing Prov.empty; Ty.generic Prov.empty @@ ty_param_nm "T#1" ] in
   let upper = Ty.inter ~prov:Prov.empty [ Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[]; Ty.generic Prov.empty @@
   ty_param_nm "T#1" ] in let body = Ty.ctor Prov.empty ~name:(ctor_nm "MyClass") ~args:[ Ty.generic Prov.empty @@
   ty_param_nm "T#2" ] in let param_bounds = Ty.Param_bounds.create ~lower ~upper () in let quants = [ Ty.Param.create
   ~name:(Located.create_empty @@ ty_param_nm "T#2") ~param_bounds () ] in Ty.exists Prov.empty ~quants ~body in let
   lower = Ty.union ~prov:Prov.empty [ Ty.nothing Prov.empty; Ty.nothing Prov.empty ] in let upper = Ty.inter
   ~prov:Prov.empty [ Ty.mixed Prov.empty; Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[] ] in let param_bounds =
   Ty.Param_bounds.create ~lower ~upper () in let quants = [ Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm
   "T#1") ~param_bounds () ] in Ty.exists Prov.empty ~quants ~body in let ty_param_refine_expect =
   Envir.Ty_param_refine.top in let expect = Ok (Refinement.replace_with ty_expect ty_param_refine_expect) in let test
   () = Alcotest.check result "" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "existential
   as test, case 1" `Quick test ;;

   let case_2 = (* Set up context *) let oracle = Oracle.( add_classishes_exn empty [ mk_class "I" ~args:[ mk_generic
   "T", Variance.Cov, Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "J" ~args: [ ( mk_generic "T" ,
   Variance.Inv , Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty) ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "A")
   ~args:[]) () , Span.empty ) ] () ; mk_class "A" () ]) in let ty_param = Envir.Ty_param.empty in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (*
   scrutinee & test types *) let t_scrut = ty_param_nm "T" in let param_bounds_scrut = Ty.Param_bounds.top Prov.empty in
   let ty_scrut = let quants = [ Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm "T")
   ~param_bounds:param_bounds_scrut () ] in let body = Ty.ctor Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic
   Prov.empty t_scrut ] in Ty.exists Prov.empty ~quants ~body in let param_bounds_test = let lower = Ty.nothing
   Prov.empty and upper = Ty.ctor Prov.empty ~name:(ctor_nm "A") ~args:[] in Ty.Param_bounds.create ~lower ~upper () in
   let ty_test = let quants = [ Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm "T")
   ~param_bounds:param_bounds_test () ] in let body = Ty.ctor Prov.empty ~name:(ctor_nm "J") ~args:[ Ty.generic
   Prov.empty @@ ty_param_nm "T" ] in Ty.exists Prov.empty ~quants ~body in (* expected result *) let ty_expect = let
   body = let quants = [ Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm "T#2")
   ~param_bounds:param_bounds_test () ] in let body = Ty.inter ~prov:Prov.(refines ~prov_scrut:Prov.empty
   ~prov_test:Prov.empty) [ Ty.ctor Prov.empty ~name:(ctor_nm "I") ~args:[ Ty.generic Prov.empty @@ ty_param_nm "T#1" ]
   ; Ty.ctor Prov.empty ~name:(ctor_nm "J") ~args:[ Ty.generic Prov.empty @@ ty_param_nm "T#2" ] ] in Ty.exists
   Prov.empty ~quants ~body in let quants = [ Ty.Param.create ~name:(Located.create_empty @@ ty_param_nm "T#1")
   ~param_bounds:param_bounds_scrut () ] in Ty.exists Prov.empty ~quants ~body in let ty_param_refine_expect =
   Envir.Ty_param_refine.top in let expect = Ok (Refinement.replace_with ty_expect ty_param_refine_expect) in let test
   () = Alcotest.check result "" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "existential
   as test, case 2" `Quick test ;;

   let test_cases = [ case_1; case_2 ] end

   module Hack_comparison = struct (** interface IInv<T> {} class C<T super int> implements IInv<T> {}

   function foo<T super int>(IInv<T> $_): void { expect<T>(1); // Ok since int <: T }

   function bar<T>(IInv<T> $x): void { if ($x is C<_>) { // We have just refined T to int <: T <: mixed so this should
   be ok expect<T>(1); // Error! 'Expected T but got int` } }

   function call_bar(): void { bar(new C<int>()); // This is fine though } *) let case_1 = (* Set up context *) let
   oracle = Oracle.( add_classishes_exn empty [ mk_class "IInv" ~args:[ Name.Ty_param.of_string "T", Variance.inv,
   Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "C" ~args: [ ( ty_param_nm "T" , Variance.Inv ,
   Ty.Param_bounds.create ~lower:(Ty.int Prov.empty) ~upper:(Ty.mixed Prov.empty) () , Span.empty ) ] ~extends:[ ctor_nm
   "IInv", [ Ty.generic Prov.empty @@ ty_param_nm "T" ] ] () ]) in let t_scrut = Name.Ty_param.Ty_param "Tscrut" in let
   t_scrut_bounds = Ty.Param_bounds.top Prov.empty in let t_test = Name.Ty_param.Ty_param "Ttest" in let t_test_bounds =
   Ty.Param_bounds.create ~lower:(Ty.int Prov.empty) ~upper:(Ty.mixed Prov.empty) () in let ty_param =
   Envir.Ty_param.(bind (bind empty t_scrut t_scrut_bounds) t_test t_test_bounds) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (*
   Scrutinee and test type *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "IInv") ~args:[ Ty.generic Prov.empty
   t_scrut ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[ Ty.generic Prov.empty t_test ] in (*
   Expected type parameter refinement *) let expect = let bnds_scrut = Ty.Param_bounds.create ~lower:(Ty.int Prov.empty)
   ~upper:(Ty.mixed Prov.empty) () in let bnds_test = Ty.Param_bounds.create ~lower:(Ty.generic Prov.empty t_scrut)
   ~upper:(Ty.generic Prov.empty t_scrut) () in Ok (Refinement.replace_with ty_test Envir.Ty_param_refine.(bounds @@
   Name.Ty_param.Map.of_alist_exn [ t_scrut, bnds_scrut; t_test, bnds_test ])) in let test () = Alcotest.check result
   "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n" (Refinement.refine
   ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement / hack comparison case 1" `Quick test ;;

   (** class Big {} class Small extends Big {} interface ICo<+T> {} class C<T as Big> implements ICo<T> {}

   function refine<T as Small>(ICo<T> $ico): void { if ($ico is C<_>) { // This should be ok since we have refined the
   bounds of the existential // to nothing <= Texists <= Small expect<C<Small>>($ico); } }

   function call(): void { refine(new C<Small>()); // This is ok though } *) let case_2 = (* Set up context *) let
   oracle = Oracle.( add_classishes_exn empty [ mk_class "ICov" ~args:[ Name.Ty_param.Ty_param "T", Variance.cov,
   Ty.Param_bounds.top Prov.empty, Span.empty ] () ; mk_class "C" ~args: [ ( Name.Ty_param.Ty_param "T" , Variance.inv ,
   Ty.Param_bounds.create ~upper:Ty.(ctor Prov.empty ~name:(ctor_nm "Big") ~args:[]) ~lower:(Ty.nothing Prov.empty) () ,
   Span.empty ) ] ~extends:[ ctor_nm "ICov", [ Ty.generic Prov.empty (ty_param_nm "T") ] ] () ]) in let t_scrut =
   Name.Ty_param.Ty_param "Tscrut" in let t_scrut_bounds = Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty)
   ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm "Small") ~args:[]) () in let t_test = Name.Ty_param.Ty_param "Ttest" in let
   t_test_bounds = Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty) ~upper:(Ty.ctor Prov.empty ~name:(ctor_nm
   "Big") ~args:[]) () in let ty_param = Envir.Ty_param.(bind (bind empty t_scrut t_scrut_bounds) t_test t_test_bounds)
   in let ty_param_refine = Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine
   ~oracle () in (* Scrutinee and test type *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICov") ~args:[
   Ty.generic Prov.empty t_scrut ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[ Ty.generic Prov.empty
   t_test ] in (* Expected type parameter refinement *) let expect = let bnds_scrut = Ty.Param_bounds.create
   ~lower:(Ty.nothing Prov.empty) ~upper:Ty.(ctor Prov.empty ~name:(ctor_nm "Big") ~args:[]) () in let bnds_test =
   Ty.Param_bounds.create ~lower:(Ty.generic Prov.empty t_scrut) ~upper:(Ty.generic Prov.empty t_scrut) () in Ok
   (Refinement.replace_with ty_test Envir.Ty_param_refine.(bounds @@ Name.Ty_param.Map.of_alist_exn [ t_scrut,
   bnds_scrut; t_test, bnds_test ])) in let test () = Alcotest.check result "\ninterface I<T>\nclass A implements
   I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in
   Alcotest.test_case "refinement / nested / hack comparison case 2" `Quick test ;;

   (** class Bigly {} class Small extends Bigly {} interface ICovContrav<+TCov, -TContrav> {} class MyClass<T super
   Small as Bigly> implements ICovContrav<T, T> {}

   function refine<T>(ICovContrav<T, T> $i): void { if ($i is MyClass<_>) { (* We should have refined: Small <= T <=
   Bigly T <= Texists <= T *) expect<T>(new Small()); // Error! Expected T but got Small } }

   function call(): void { refine(new MyClass<Small>()); // This is ok, though refine(new MyClass<Bigly>()); // and so
   is this }

   *) let case_3 = (* Set up context *) let oracle = Oracle.( add_classishes_exn empty [ ctor_nm "Bigly", [], [] ;
   ctor_nm "Small", [], [ ctor_nm "Bigly", [] ] ; ( Name.Ctor.Ctor "ICovContrav" , [ Name.Ty_param.Ty_param "TCov",
   Variance.cov, Ty.Param_bounds.top Prov.empty, Span.empty ; Name.Ty_param.Ty_param "TContrav", Variance.contrav,
   Ty.Param_bounds.top Prov.empty, Span.empty ] , [] ) ; ( Name.Ctor.Ctor "C" , [ ( Name.Ty_param.Ty_param "T" ,
   Variance.inv , Ty.Param_bounds.create ~lower:Ty.(ctor Prov.empty ~name:(ctor_nm "Small") ~args:[]) ~upper:Ty.(ctor
   Prov.empty ~name:(ctor_nm "Bigly") ~args:[]) () , Span.empty ) ] , [ ( ctor_nm "ICovContrav" , Ty.[ generic
   Prov.empty (ty_param_nm "T"); generic Prov.empty (ty_param_nm "T") ] ) ] ) ]) in let small = Ty.ctor Prov.empty
   ~name:(ctor_nm "Small") ~args:[] and bigly = Ty.ctor Prov.empty ~name:(ctor_nm "Bigly") ~args:[] in let t_scrut =
   Name.Ty_param.Ty_param "Tscrut" in let t_scrut_bounds = Ty.Param_bounds.top Prov.empty in let t_test =
   Name.Ty_param.Ty_param "Ttest" in let t_test_bounds = Ty.Param_bounds.create ~lower:small ~upper:bigly () in let
   ty_param = Envir.Ty_param.(bind (bind empty t_scrut t_scrut_bounds) t_test t_test_bounds) in let ty_param_refine =
   Envir.Ty_param_refine.empty in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (*
   Scrutinee and test type *) let ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICovContrav") ~args:Ty.[ generic
   Prov.empty t_scrut; generic Prov.empty t_scrut ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[
   Ty.generic Prov.empty t_test ] in (* Expected type parameter refinement *) let expect = let bnds_scrut =
   Ty.Param_bounds.create ~lower:Ty.(union [ small; small ] ~prov:Prov.empty) ~upper:Ty.(inter [ bigly; bigly ]
   ~prov:Prov.empty) () in let bnds_test = let ty_t_scrut = Ty.generic Prov.empty t_scrut in Ty.Param_bounds.create
   ~lower:Ty.(union [ ty_t_scrut; ty_t_scrut ] ~prov:Prov.empty) ~upper:Ty.(inter [ ty_t_scrut; ty_t_scrut ]
   ~prov:Prov.empty) () in Ok (Refinement.replace_with Ty.( ctor Prov.empty ~name:(ctor_nm "C") ~args:[ inter [ generic
   Prov.empty t_test; generic Prov.empty t_test ] ~prov:Prov.empty ]) Envir.Ty_param_refine.(bounds @@
   Name.Ty_param.Map.of_alist_exn [ t_scrut, bnds_scrut; t_test, bnds_test ])) in let test () = Alcotest.check result
   "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n" (Refinement.refine
   ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement / hack comparison case 3" `Quick test ;;

   (* class Bigly {} class Small extends Bigly {}

   interface ICovContrav<+T1, -T2> {}

   class C<T> implements ICovContrav<T, T> {}

   function refine<T1 as Big, T2 super Small>( ICovContrav<T1, T2> $i, ): ?ICovContrav<T1, T2> { if ($i is C<_>) {
   hh_show_env(); } return null;

   } *) let case_4 = (* Set up context *) let oracle = Oracle.( add_classishes_exn empty [ ctor_nm "Bigly", [], [] ;
   ctor_nm "Small", [], [ ctor_nm "Bigly", [] ] ; ( Name.Ctor.Ctor "ICovContrav" , [ Name.Ty_param.Ty_param "TCov",
   Variance.cov, Ty.Param_bounds.top Prov.empty, Span.empty ; Name.Ty_param.Ty_param "TContrav", Variance.contrav,
   Ty.Param_bounds.top Prov.empty, Span.empty ] , [] ) ; ( Name.Ctor.Ctor "C" , [ Name.Ty_param.Ty_param "T",
   Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ] , [ ( ctor_nm "ICovContrav" , Ty.[ generic Prov.empty
   (ty_param_nm "T"); generic Prov.empty (ty_param_nm "T") ] ) ] ) ]) in let small = Ty.ctor Prov.empty ~name:(ctor_nm
   "Small") ~args:[] and bigly = Ty.ctor Prov.empty ~name:(ctor_nm "Bigly") ~args:[] in let t_scrut1 =
   Name.Ty_param.Ty_param "Tscrut1" in let t_scrut1_bounds = Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty)
   ~upper:bigly () in let t_scrut2 = Name.Ty_param.Ty_param "Tscrut2" in let t_scrut2_bounds = Ty.Param_bounds.create
   ~upper:(Ty.mixed Prov.empty) ~lower:small () in let t_test = Name.Ty_param.Ty_param "Ttest" in let t_test_bounds =
   Ty.Param_bounds.create ~lower:small ~upper:bigly () in let ty_param = Envir.Ty_param.(bind (bind (bind empty t_scrut1
   t_scrut1_bounds) t_scrut2 t_scrut2_bounds) t_test t_test_bounds) in let ty_param_refine = Envir.Ty_param_refine.empty
   in let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in (* Scrutinee and test type *) let
   ty_scrut = Ty.ctor Prov.empty ~name:(ctor_nm "ICovContrav") ~args:Ty.[ generic Prov.empty t_scrut1; generic
   Prov.empty t_scrut2 ] in let ty_test = Ty.ctor Prov.empty ~name:(ctor_nm "C") ~args:[ Ty.generic Prov.empty t_test ]
   in (* Expected type parameter refinement *) let expect = let bnds_scrut = Ty.Param_bounds.create ~lower:Ty.(union [
   small; small ] ~prov:Prov.empty) ~upper:Ty.(inter [ bigly; bigly ] ~prov:Prov.empty) () in let bnds_test = let
   ty_t_scrut = Ty.generic Prov.empty t_scrut1 in Ty.Param_bounds.create ~lower:Ty.(union [ ty_t_scrut; ty_t_scrut ]
   ~prov:Prov.empty) ~upper:Ty.(inter [ ty_t_scrut; ty_t_scrut ] ~prov:Prov.empty) () in Ok (Refinement.replace_with
   Ty.( ctor Prov.empty ~name:(ctor_nm "C") ~args:[ inter [ generic Prov.empty t_test; generic Prov.empty t_test ]
   ~prov:Prov.empty ]) Envir.Ty_param_refine.(bounds @@ Name.Ty_param.Map.of_alist_exn [ t_scrut1, bnds_scrut; t_test,
   bnds_test ])) in let test () = Alcotest.check result "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = {
   nothing <= Ta <= Four }\n" (Refinement.refine ~ty_scrut ~ty_test ~ctxt) expect in Alcotest.test_case "refinement /
   hack comparison case 4" `Quick test ;;

   let test_cases = [ case_1; case_2; case_3; case_4 ] end

   let test_cases = List.concat [ Gadt_covariant.test_cases ; Invariant_class_impl_covariant.test_cases ;
   Non_generic_class_impl_covariant.test_cases ; Nested.test_cases ; Union_scrut.test_cases ; Union_test.test_cases ;
   Intersection_scrut.test_cases ; Intersection_test.test_cases ; Existential_test.test_cases ;
   Existential_both.test_cases ; Hack_comparison.test_cases ] ;; *)
