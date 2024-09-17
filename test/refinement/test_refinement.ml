open Core
open Common
open Test_common

module Down = struct
  let result = Alcotest.result Testable.ty_param_refine Testable.refinement_err
  let ctor_nm nm = Identifier.Ctor.Ctor nm
  let mk_class nm ?(args = []) ?(extends = []) () = ctor_nm nm, args, extends
  let ty_param_nm nm = Identifier.Ty_param.Ty_param nm
  let mk_generic nm = Ty.Generic.Generic (ty_param_nm nm)

  let class_chain =
    [ mk_class "Seven" ()
    ; mk_class "Six" ~extends:[ ctor_nm "Seven", [] ] ()
    ; mk_class "Five" ~extends:[ ctor_nm "Six", [] ] ()
    ; mk_class "Four" ~extends:[ ctor_nm "Five", [] ] ()
    ; mk_class "Three" ~extends:[ ctor_nm "Four", [] ] ()
    ; mk_class "Two" ~extends:[ ctor_nm "Three", [] ] ()
    ; mk_class "One" ~extends:[ ctor_nm "Two", [] ] ()
    ]
  ;;

  module Gadt_covariant = struct
    let oracle =
      Oracle.(
        add_classishes_exn
          empty
          (class_chain
           @ [ ( Identifier.Ctor.Ctor "I"
               , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.cov, Ty.Param_bounds.top ]
               , [] )
             ; Identifier.Ctor.Ctor "A", [], [ Identifier.Ctor.Ctor "I", [ Ty.ctor (ctor_nm "Four") [] ] ]
             ]))
    ;;

    let agreement =
      (* Scrutinee and test type *)
      let ta = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ta") in
      let ty_scrut = Ty.ctor (ctor_nm "I") [ Ty.Generic ta ]
      and ty_test = Ty.ctor (ctor_nm "A") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty ta Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let four = Ty.ctor (ctor_nm "Four") [] in
        Ok Envir.Ty_param_refine.(singleton ta @@ Ty.Param_bounds.create ~lower_bound:four ~upper_bound:four ())
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / down / gadt refinement with agreement between bounds" `Quick test
    ;;

    let disagreement =
      (* Scrutinee and test type *)
      let ta = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ta") in
      let ty_scrut = Ty.ctor (ctor_nm "I") [ Ty.Generic ta ] in
      let ty_test = Ty.ctor (ctor_nm "A") [] in
      (* Set up context *)
      let three = Ty.ctor (ctor_nm "Three") []
      and four = Ty.ctor (ctor_nm "Four") [] in
      let ta_bounds = Ty.Param_bounds.create ~upper_bound:three () in
      let ty_param = Envir.Ty_param.(bind empty ta ta_bounds) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        Ok
          Envir.Ty_param_refine.(
            singleton ta @@ Ty.Param_bounds.create ~lower_bound:four ~upper_bound:(Ty.inter [ four ]) ())
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<int> {}\nI<Ta> ↓ A = { One | Four <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / down / gadt refinement with agreement between bounds" `Quick test
    ;;

    let test_cases = [ agreement; disagreement ]
  end

  module Invariant_class_impl_covariant = struct
    let oracle =
      Oracle.(
        add_classishes_exn
          empty
          ([ mk_class "ICo" ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top ] ()
           ; mk_class
               "MyClass"
               ~args:
                 [ ( mk_generic "T"
                   , Variance.Inv
                   , Ty.Param_bounds.create
                       ~lower_bound:(Ty.ctor (ctor_nm "Two") [])
                       ~upper_bound:(Ty.ctor (ctor_nm "Six") [])
                       () )
                 ]
               ~extends:[ ctor_nm "ICo", [ Ty.generic @@ ty_param_nm "T" ] ]
               ()
           ]
           @ class_chain))
    ;;

    (* ; mk_class "CConcreteImplICo" ~extends:[ ctor_nm "ICo", [ Ty.ctor (ctor_nm "Four") [] ] ] ()
          ; mk_class
              "CImplIContra"
              ~args:
                [ ( mk_generic "T"
                  , Variance.Inv
                  , Ty.Param_bounds.create
                      ~lower_bound:(Ty.ctor (ctor_nm "Two") [])
                      ~upper_bound:(Ty.ctor (ctor_nm "Six") [])
                      () )
                ]
              ~extends:[ ctor_nm "IContra", [ Ty.generic @@ ty_param_nm "T" ] ]
              ()
          ; mk_class
              "CImplIInv"
              ~args:
                [ ( mk_generic "T"
                  , Variance.Inv
                  , Ty.Param_bounds.create
                      ~lower_bound:(Ty.ctor (ctor_nm "Two") [])
                      ~upper_bound:(Ty.ctor (ctor_nm "Six") [])
                      () )
                ]
              ~extends:[ ctor_nm "IInv", [ Ty.generic @@ ty_param_nm "T" ] ]
              ()
          ]) *)

    let doc_case_1 =
      (* Scrutinee and test types *)
      let ty_scrut = Ty.ctor (ctor_nm "ICo") Ty.[ ctor (ctor_nm "Four") [] ] in
      let ty_test = Ty.ctor (ctor_nm "MyClass") Ty.[ generic @@ ty_param_nm "Ta" ] in
      (* Set up context *)
      let ta = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ta") in
      let ty_param =
        Envir.Ty_param.(
          bind empty ta
          @@ Ty.Param_bounds.create
               ~lower_bound:(Ty.ctor (ctor_nm "Two") [])
               ~upper_bound:(Ty.ctor (ctor_nm "Six") [])
               ())
      in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinements *)
      let expect =
        Ok (Envir.Ty_param_refine.singleton ta @@ Ty.Param_bounds.create ~upper_bound:Ty.(ctor (ctor_nm "Four") []) ())
      in
      let test () =
        Alcotest.check
          result
          "\n\
           interface ICo<+T>\n\
           class MyClass<T super Two as Six> extends ICo<T> {}\n\
           Γ, Two <= Ta <= Six ⊢ ICo<Four> ↓ CImplCo<Ta> = {Ta <= Four}\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / down / invariant class implementing covariant interface / doc case 1" `Quick test
    ;;

    let doc_case_2 =
      (* Scrutinee and test types *)
      let ty_scrut = Ty.ctor (ctor_nm "ICo") Ty.[ ctor (ctor_nm "One") [] ] in
      let ty_test = Ty.ctor (ctor_nm "MyClass") Ty.[ generic @@ ty_param_nm "Ta" ] in
      (* Set up context *)
      let ta = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ta") in
      let ty_param =
        Envir.Ty_param.(
          bind empty ta
          @@ Ty.Param_bounds.create
               ~lower_bound:(Ty.ctor (ctor_nm "Two") [])
               ~upper_bound:(Ty.ctor (ctor_nm "Six") [])
               ())
      in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinements *)
      let bounds_expect = Ty.Param_bounds.create ~upper_bound:Ty.(ctor (ctor_nm "One") []) () in
      let expect = Ok Envir.Ty_param_refine.(singleton ta bounds_expect) in
      let test () =
        Alcotest.check
          result
          "\n\
           interface ICo<+T>\n\
           class MyClass<T super Two as Six> extends ICo<T> {}\n\
           Γ, Two <= Ta <= Six ⊢ ICo<One> ↓ CImplCo<Ta> = {Ta <= One}\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / down / invariant class implementing covariant interface / doc case 2" `Quick test
    ;;

    let doc_case_3 =
      (* Scrutinee and test types *)
      let ty_scrut = Ty.ctor (ctor_nm "ICo") Ty.[ ctor (ctor_nm "Seven") [] ] in
      let ty_test = Ty.ctor (ctor_nm "MyClass") Ty.[ generic @@ ty_param_nm "Ta" ] in
      (* Set up context *)
      let ta = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ta") in
      let ty_param =
        Envir.Ty_param.(
          bind empty ta
          @@ Ty.Param_bounds.create
               ~lower_bound:(Ty.ctor (ctor_nm "Two") [])
               ~upper_bound:(Ty.ctor (ctor_nm "Six") [])
               ())
      in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinements *)
      let bounds_expect = Ty.Param_bounds.create ~upper_bound:Ty.(ctor (ctor_nm "Seven") []) () in
      let expect = Ok Envir.Ty_param_refine.(singleton ta bounds_expect) in
      let test () =
        Alcotest.check
          result
          "\n\
           interface ICo<+T>\n\
           class MyClass<T super Two as Six> extends ICo<T> {}\n\
           Γ, Two <= Ta <= Six ⊢ ICo<Seven> ↓ CImplCo<Ta> = {Ta <= Seven}\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / down / invariant class implementing covariant interface / doc case 3" `Quick test
    ;;

    let doc_case_4 =
      let ty_scrut = Ty.ctor (ctor_nm "ICo") Ty.[ generic @@ ty_param_nm "Tco" ] in
      let ty_test = Ty.ctor (ctor_nm "MyClass") Ty.[ generic @@ ty_param_nm "Ta" ] in
      let ta = mk_generic "Ta"
      and tco = mk_generic "Tco" in
      let ta_bounds =
        Ty.Param_bounds.create ~lower_bound:(Ty.ctor (ctor_nm "Two") []) ~upper_bound:(Ty.ctor (ctor_nm "Six") []) ()
      and tco_bounds =
        Ty.Param_bounds.create ~lower_bound:(Ty.ctor (ctor_nm "Four") []) ~upper_bound:(Ty.ctor (ctor_nm "Six") []) ()
      in
      let ty_param = Envir.Ty_param.(bind (bind empty ta ta_bounds) tco tco_bounds) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      let tco_bounds_expect = ta_bounds in
      let ta_bounds_expect =
        Ty.Param_bounds.create
          ~lower_bound:Ty.(generic @@ ty_param_nm "Tco")
          ~upper_bound:Ty.(generic @@ ty_param_nm "Tco")
          ()
      in
      let expect =
        Ok (Envir.Ty_param_refine.bounds @@ Ty.Generic.Map.of_alist_exn [ ta, ta_bounds_expect; tco, tco_bounds_expect ])
      in
      let test () =
        Alcotest.check
          result
          "\n\
           interface ICo<+T>\n\
           class MyClass<T super Two as Six> extends ICo<T> {}\n\
           Γ, Two <= Ta <= Six, Four <= Tco <= Six ⊢ ICo<Tco> ↓ CImplCo<Ta> = {Ta <= Seven}\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / down / invariant class implementing covariant interface / doc case 4" `Quick test
    ;;

    let test_cases = [ doc_case_1; doc_case_2; doc_case_3; doc_case_4 ]
  end

  module Non_generic_class_impl_covariant = struct
    let oracle =
      Oracle.(
        add_classishes_exn
          empty
          [ mk_class "Seven" ()
          ; mk_class "Six" ~extends:[ ctor_nm "Seven", [] ] ()
          ; mk_class "Five" ~extends:[ ctor_nm "Six", [] ] ()
          ; mk_class "Four" ~extends:[ ctor_nm "Five", [] ] ()
          ; mk_class "Three" ~extends:[ ctor_nm "Four", [] ] ()
          ; mk_class "Two" ~extends:[ ctor_nm "Three", [] ] ()
          ; mk_class "One" ~extends:[ ctor_nm "Two", [] ] ()
          ; mk_class "ICo" ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top ] ()
          ; mk_class "MyClass" ~extends:[ ctor_nm "ICo", [ Ty.ctor (ctor_nm "Four") [] ] ] ()
          ])
    ;;

    let doc_case_1 =
      (* Scrutinee and test types *)
      let ty_scrut = Ty.ctor (ctor_nm "ICo") Ty.[ ctor (ctor_nm "Two") [] ] in
      let ty_test = Ty.ctor (ctor_nm "MyClass") [] in
      (* Set up refinement context *)
      let ty_param = Envir.Ty_param.empty in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expect no type parameter refinement *)
      let expect =
        Error
          (Refinement.Err.Multiple
             [ Refinement.Err.Not_a_subclass (Identifier.Ctor.Minimal.Ctor "Two", Identifier.Ctor.Minimal.Ctor "Four") ])
      in
      let test () =
        Alcotest.check
          result
          "\ninterface ICo<+T>\nclass MyClass extends ICo<Four> {}\nICo<Two> ↓ MyClass = err\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case
        "refinement / down / non-generic class implementing covariant interface / doc case 1"
        `Quick
        test
    ;;

    let doc_case_2 =
      (* Scrutinee and test types *)
      let ty_scrut = Ty.ctor (ctor_nm "ICo") Ty.[ ctor (ctor_nm "Six") [] ] in
      let ty_test = Ty.ctor (ctor_nm "MyClass") [] in
      (* Set up refinement context *)
      let ty_param = Envir.Ty_param.empty in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expect no type parameter refinement *)
      let expect = Ok Envir.Ty_param_refine.top in
      let test () =
        Alcotest.check
          result
          "\ninterface ICo<+T>\nclass MyClass extends ICo<Four> {}\nICo<Two> ↓ MyClass = {}\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case
        "refinement / down / non-generic class implementing covariant interface / doc case 1"
        `Quick
        test
    ;;

    let test_cases = [ doc_case_2; doc_case_1 ]
  end

  module Nested = struct
    let akenn1 =
      (*
         class B<Tb> {}
         class A<Ta> {}
         class C {}
         class D extends A<B<C>> {} *)
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ mk_class "B" ~args:[ mk_generic "Tb", Variance.Inv, Ty.Param_bounds.top ] ()
            ; mk_class "A" ~args:[ mk_generic "Ta", Variance.Inv, Ty.Param_bounds.top ] ()
            ; mk_class "C" ()
            ; mk_class "D" ~extends:[ ctor_nm "A", [ Ty.ctor (ctor_nm "B") [ Ty.ctor (ctor_nm "C") [] ] ] ] ()
            ])
      in
      (* Scrutinee and test type *)
      let tab = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tab") in
      let ty_scrut =
        let b = Ty.ctor (ctor_nm "B") [ Ty.Generic tab ] in
        Ty.ctor (ctor_nm "A") [ b ]
      in
      let ty_test = Ty.ctor (ctor_nm "D") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty tab Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let c = Ty.ctor (ctor_nm "C") [] in
        let bnds = Ty.Param_bounds.create ~lower_bound:(Ty.union [ c; c ]) ~upper_bound:(Ty.inter [ c; c ]) () in
        Ok Envir.Ty_param_refine.(singleton tab bnds)
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / nested / nested case" `Quick test
    ;;

    let akenn2 =
      (*
         class B<Tb> {}
         class A<-Ta> {}
         class C {}
         class D extends A<B<C>> {} 
         class E<Te> extends B<Te> *)
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ mk_class "B" ~args:[ mk_generic "Tb", Variance.Inv, Ty.Param_bounds.top ] ()
            ; mk_class "A" ~args:[ mk_generic "Ta", Variance.Contrav, Ty.Param_bounds.top ] ()
            ; mk_class "C" ()
            ; mk_class "D" ~extends:[ ctor_nm "A", [ Ty.ctor (ctor_nm "B") [ Ty.ctor (ctor_nm "C") [] ] ] ] ()
            ; mk_class
                "E"
                ~args:[ mk_generic "Te", Variance.Inv, Ty.Param_bounds.top ]
                ~extends:[ ctor_nm "B", [ Ty.Generic (mk_generic "Te") ] ]
                ()
            ])
      in
      (* Scrutinee and test type *)
      let tae = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tae") in
      let ty_scrut =
        let b = Ty.ctor (ctor_nm "E") [ Ty.Generic tae ] in
        Ty.ctor (ctor_nm "A") [ b ]
      in
      let ty_test = Ty.ctor (ctor_nm "D") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty tae Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let c = Ty.ctor (ctor_nm "C") [] in
        Ok Envir.Ty_param_refine.(singleton tae @@ Ty.Param_bounds.create ~lower_bound:c ~upper_bound:c ())
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / nested / nested case 2" `Quick test
    ;;

    let test_cases = [ akenn1; akenn2 ]
  end

  let test_cases =
    List.concat
      [ Gadt_covariant.test_cases
      ; Invariant_class_impl_covariant.test_cases
      ; Non_generic_class_impl_covariant.test_cases
      ; Nested.test_cases
      ]
  ;;
end

let test_cases = List.concat [ Down.test_cases ]
