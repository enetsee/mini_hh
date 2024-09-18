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
         class E<Te> extends B<Te> 
         
         A<E<Tab>> ~~> D
      *)
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

    let akenn3 =
      (*
         class B<Tb> {}
         class A<+Ta> {}
         class C {}
         class D extends A<B<C>> {} *)
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ mk_class "B" ~args:[ mk_generic "Tb", Variance.Inv, Ty.Param_bounds.top ] ()
            ; mk_class "A" ~args:[ mk_generic "Ta", Variance.Cov, Ty.Param_bounds.top ] ()
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
        let bnds = Ty.Param_bounds.create ~lower_bound:c ~upper_bound:c () in
        Ok Envir.Ty_param_refine.(singleton tab bnds)
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / nested / nested case 3" `Quick test
    ;;

    (**
      class Inv<T> {}
      class SubInv<T> extends Inv<T> {}
      class Contrav<-T> {}
      class SubContrav extends Contrav<Cov<Inv<End>>> {}
      class Cov<+T> {}
      class SubCov<+T> extends Cov<T> {}
      class End {}

      function refine<T>(Contrav<SubCov<SubInv<T>>> $scrut): void {
        if ($scrut is SubContrav) {
          expect<T>(new End());
        }
      } 
    *)
    let akenn4 =
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ mk_class "Inv" ~args:[ mk_generic "T", Variance.Inv, Ty.Param_bounds.top ] ()
            ; mk_class
                "SubInv"
                ~args:[ mk_generic "T", Variance.Inv, Ty.Param_bounds.top ]
                ~extends:[ ctor_nm "Inv", [ Ty.generic (ty_param_nm "T") ] ]
                ()
            ; mk_class "Cov" ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top ] ()
            ; mk_class
                "SubCov"
                ~args:[ mk_generic "T", Variance.Cov, Ty.Param_bounds.top ]
                ~extends:[ ctor_nm "Cov", [ Ty.generic (ty_param_nm "T") ] ]
                ()
            ; mk_class "End" ()
            ; mk_class "Contrav" ~args:[ mk_generic "T", Variance.Contrav, Ty.Param_bounds.top ] ()
            ; mk_class
                "SubContrav"
                ~extends:
                  [ (ctor_nm "Contrav", Ty.[ ctor (ctor_nm "Cov") [ ctor (ctor_nm "Inv") [ ctor (ctor_nm "End") [] ] ] ])
                  ]
                ()
            ])
      in
      (* Scrutinee and test type *)
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let ty_scrut =
        Ty.(ctor (ctor_nm "Contrav") [ ctor (ctor_nm "SubCov") [ ctor (ctor_nm "SubInv") [ Generic t_scrut ] ] ])
      in
      let ty_test = Ty.ctor (ctor_nm "SubContrav") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty t_scrut Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let c = Ty.ctor (ctor_nm "End") [] in
        let bnds = Ty.Param_bounds.create ~lower_bound:c ~upper_bound:c () in
        Ok Envir.Ty_param_refine.(singleton t_scrut bnds)
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / nested / nested case 4" `Quick test
    ;;

    let test_cases = [ akenn1; akenn2; akenn3; akenn4 ]
  end

  module Union = struct
    (*
       interface I<T> {}
    interface J<T> {}
    interface K {}
    class E implements I<Four>, J<Five>, K {}

    (I<T> | J<T>) is E 

    Should let us refine T to int

    But,  

    (I<T> | K)  is E 

    shouldn't let us refine T *)

    let oracle =
      Oracle.(
        add_classishes_exn
          empty
          (class_chain
           @ [ ( Identifier.Ctor.Ctor "I"
               , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
               , [] )
             ; ( Identifier.Ctor.Ctor "J"
               , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
               , [] )
             ; Identifier.Ctor.Ctor "K", [], []
             ; ( Identifier.Ctor.Ctor "E"
               , []
               , [ ctor_nm "I", [ Ty.ctor (ctor_nm "Four") [] ]
                 ; ctor_nm "J", [ Ty.ctor (ctor_nm "Five") [] ]
                 ; ctor_nm "K", []
                 ] )
             ; Identifier.Ctor.Ctor "F", [], [ ctor_nm "I", [ Ty.ctor (ctor_nm "Four") [] ] ]
             ]))
    ;;

    let case_1 =
      (* Scrutinee and test type *)
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let ty_scrut =
        let i = Ty.ctor (ctor_nm "I") [ Ty.Generic t_scrut ] in
        let j = Ty.ctor (ctor_nm "J") [ Ty.Generic t_scrut ] in
        Ty.union [ i; j ]
      in
      let ty_test = Ty.ctor (ctor_nm "E") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty t_scrut Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let four = Ty.ctor (ctor_nm "Four") [] in
        let five = Ty.ctor (ctor_nm "Five") [] in
        let bnds =
          Ty.Param_bounds.create ~lower_bound:(Ty.union [ five; four ]) ~upper_bound:(Ty.inter [ five; four ]) ()
        in
        Ok Envir.Ty_param_refine.(singleton t_scrut bnds)
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / union case 1" `Quick test
    ;;

    let case_2 =
      (* Scrutinee and test type *)
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let ty_scrut =
        let i = Ty.ctor (ctor_nm "I") [ Ty.Generic t_scrut ] in
        let k = Ty.ctor (ctor_nm "K") [] in
        Ty.union [ i; k ]
      in
      let ty_test = Ty.ctor (ctor_nm "E") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty t_scrut Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let lower_bound = Ty.ctor (ctor_nm "Four") [] in
        let upper_bound = lower_bound in
        Ok (Envir.Ty_param_refine.singleton t_scrut @@ Ty.Param_bounds.create ~upper_bound ~lower_bound ())
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / union case 2" `Quick test
    ;;

    let case_3 =
      (* Scrutinee and test type *)
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let ty_scrut =
        let i = Ty.ctor (ctor_nm "I") [ Ty.Generic t_scrut ] in
        let j = Ty.ctor (ctor_nm "J") [ Ty.Generic t_scrut ] in
        Ty.union [ i; j ]
      in
      let ty_test = Ty.ctor (ctor_nm "F") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty t_scrut Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let lower_bound = Ty.ctor (ctor_nm "Four") [] in
        let upper_bound = lower_bound in
        Ok (Envir.Ty_param_refine.singleton t_scrut @@ Ty.Param_bounds.create ~upper_bound ~lower_bound ())
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / union case 3" `Quick test
    ;;

    let test_cases = [ case_1; case_2; case_3 ]
  end

  module Intersection = struct
    let oracle =
      Oracle.(
        add_classishes_exn
          empty
          (class_chain
           @ [ ( Identifier.Ctor.Ctor "I"
               , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
               , [] )
             ; Identifier.Ctor.Ctor "K", [], []
             ; Identifier.Ctor.Ctor "C", [], [ ctor_nm "I", [ Ty.ctor (ctor_nm "Four") [] ]; ctor_nm "K", [] ]
             ; Identifier.Ctor.Ctor "D", [], [ ctor_nm "I", [ Ty.ctor (ctor_nm "Four") [] ] ]
             ]))
    ;;

    let case_1 =
      (* Scrutinee and test type *)
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let ty_scrut =
        let i = Ty.ctor (ctor_nm "I") [ Ty.Generic t_scrut ] in
        let k = Ty.ctor (ctor_nm "K") [] in
        Ty.inter [ i; k ]
      in
      let ty_test = Ty.ctor (ctor_nm "C") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty t_scrut Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let four = Ty.ctor (ctor_nm "Four") [] in
        let bnds = Ty.Param_bounds.create ~lower_bound:four ~upper_bound:four () in
        Ok Envir.Ty_param_refine.(singleton t_scrut bnds)
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / intersection case 1" `Quick test
    ;;

    let case_2 =
      (* Scrutinee and test type *)
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let ty_scrut =
        let i = Ty.ctor (ctor_nm "I") [ Ty.Generic t_scrut ] in
        let k = Ty.ctor (ctor_nm "K") [] in
        Ty.inter [ i; k ]
      in
      let ty_test = Ty.ctor (ctor_nm "D") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty t_scrut Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        Error
          (Refinement.Err.Multiple
             [ Refinement.Err.Not_a_subclass (Identifier.Ctor.Minimal.Ctor "K", Identifier.Ctor.Minimal.Ctor "D") ])
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / intersecrtion case 2" `Quick test
    ;;

    let oracle =
      Oracle.(
        add_classishes_exn
          empty
          (class_chain
           @ [ ( Identifier.Ctor.Ctor "I"
               , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
               , [] )
             ; ( Identifier.Ctor.Ctor "J"
               , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
               , [] )
             ; Identifier.Ctor.Ctor "K", [], []
             ; ( Identifier.Ctor.Ctor "E"
               , []
               , [ ctor_nm "I", [ Ty.ctor (ctor_nm "Four") [] ]
                 ; ctor_nm "J", [ Ty.ctor (ctor_nm "Five") [] ]
                 ; ctor_nm "K", []
                 ] )
             ]))
    ;;

    let case_3 =
      (* Scrutinee and test type *)
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let ty_scrut =
        let i = Ty.ctor (ctor_nm "I") [ Ty.Generic t_scrut ] in
        let j = Ty.ctor (ctor_nm "J") [ Ty.Generic t_scrut ] in
        Ty.inter [ i; j ]
      in
      let ty_test = Ty.ctor (ctor_nm "E") [] in
      (* Set up context *)
      let ty_param = Envir.Ty_param.(bind empty t_scrut Ty.Param_bounds.top) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Expected type parameter refinement *)
      let expect =
        let four = Ty.ctor (ctor_nm "Four") [] in
        let five = Ty.ctor (ctor_nm "Five") [] in
        let bnds =
          Ty.Param_bounds.create ~lower_bound:(Ty.inter [ five; four ]) ~upper_bound:(Ty.union [ five; four ]) ()
        in
        Ok Envir.Ty_param_refine.(singleton t_scrut bnds)
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / intersection case 3" `Quick test
    ;;

    let test_cases = [ case_1; case_2 ]
  end

  module Hack_comparison = struct
    (**
        interface IInv<T> {}
        class C<T super int> implements IInv<T> {}

        function foo<T super int>(IInv<T> $_): void {
          expect<T>(1); // Ok since int <: T
        }

        function bar<T>(IInv<T> $x): void {
         if ($x is C<_>) {
          // We have just refined T to int <: T <: mixed so this should be ok
          expect<T>(1); // Error! 'Expected T but got int`
         }
       }

       function call_bar(): void {
        bar(new C<int>()); // This is fine though
       }
    *)
    let case_1 =
      (* Set up context *)
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Identifier.Ctor.Ctor "IInv"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [] )
            ; ( Identifier.Ctor.Ctor "C"
              , [ ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.create ~lower_bound:Ty.int () )
                ]
              , [ ctor_nm "IInv", [ Ty.generic (ty_param_nm "T") ] ] )
            ])
      in
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let t_scrut_bounds = Ty.Param_bounds.top in
      let t_test = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ttest") in
      let t_test_bounds = Ty.Param_bounds.create ~lower_bound:Ty.int () in
      let ty_param = Envir.Ty_param.(bind (bind empty t_scrut t_scrut_bounds) t_test t_test_bounds) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Scrutinee and test type *)
      let ty_scrut = Ty.ctor (ctor_nm "IInv") [ Ty.Generic t_scrut ] in
      let ty_test = Ty.ctor (ctor_nm "C") [ Ty.Generic t_test ] in
      (* Expected type parameter refinement *)
      let expect =
        let bnds_scrut = Ty.Param_bounds.create ~lower_bound:Ty.int () in
        let bnds_test = Ty.Param_bounds.create ~lower_bound:(Ty.Generic t_scrut) ~upper_bound:(Ty.Generic t_scrut) () in
        Ok Envir.Ty_param_refine.(bounds @@ Ty.Generic.Map.of_alist_exn [ t_scrut, bnds_scrut; t_test, bnds_test ])
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / nested / hack comparison case 1" `Quick test
    ;;

    (** 
      class Big {}
      class Small extends Big {}
      interface ICo<+T> {}
      class C<T as Big> implements ICo<T> {}

      function refine<T as Small>(ICo<T> $ico): void {
        if ($ico is C<_>) {
          // This should be ok since we have refined the bounds of the existential
          // to nothing <= Texists <= Small
          expect<C<Small>>($ico);
        }
      }

      function call(): void {
        refine(new C<Small>()); // This is ok though
      } 
   *)
    let case_2 =
      (* Set up context *)
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Identifier.Ctor.Ctor "ICov"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.cov, Ty.Param_bounds.top ]
              , [] )
            ; ( Identifier.Ctor.Ctor "C"
              , [ ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.create ~upper_bound:Ty.(ctor (ctor_nm "Big") []) () )
                ]
              , [ ctor_nm "ICov", [ Ty.generic (ty_param_nm "T") ] ] )
            ])
      in
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let t_scrut_bounds = Ty.Param_bounds.create ~upper_bound:(Ty.ctor (ctor_nm "Small") []) () in
      let t_test = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ttest") in
      let t_test_bounds = Ty.Param_bounds.create ~upper_bound:(Ty.ctor (ctor_nm "Big") []) () in
      let ty_param = Envir.Ty_param.(bind (bind empty t_scrut t_scrut_bounds) t_test t_test_bounds) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Scrutinee and test type *)
      let ty_scrut = Ty.ctor (ctor_nm "ICov") [ Ty.Generic t_scrut ] in
      let ty_test = Ty.ctor (ctor_nm "C") [ Ty.Generic t_test ] in
      (* Expected type parameter refinement *)
      let expect =
        let bnds_scrut = Ty.Param_bounds.create ~upper_bound:Ty.(ctor (ctor_nm "Big") []) () in
        let bnds_test = Ty.Param_bounds.create ~lower_bound:(Ty.Generic t_scrut) ~upper_bound:(Ty.Generic t_scrut) () in
        Ok Envir.Ty_param_refine.(bounds @@ Ty.Generic.Map.of_alist_exn [ t_scrut, bnds_scrut; t_test, bnds_test ])
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / nested / hack comparison case 2" `Quick test
    ;;

    (**  
    class Bigly {}
    class Small extends Bigly {}
    interface ICovContrav<+TCov, -TContrav> {}
    class MyClass<T super Small as Bigly> implements ICovContrav<T, T> {}

    function refine<T>(ICovContrav<T, T> $i): void {
      if ($i is MyClass<_>) {
        (* We should have refined:
           Small <= T <= Bigly
           T <= Texists <= T *)
        expect<T>(new Small()); // Error! Expected T but got Small
      }
    }

    function call(): void {
      refine(new MyClass<Small>()); // This is ok, though
      refine(new MyClass<Bigly>()); // and so is this
    }
              
    *)
    let case_3 =
      (* Set up context *)
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ctor_nm "Bigly", [], []
            ; ctor_nm "Small", [], [ ctor_nm "Bigly", [] ]
            ; ( Identifier.Ctor.Ctor "ICovContrav"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "TCov"), Variance.cov, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "TContrav"), Variance.contrav, Ty.Param_bounds.top
                ]
              , [] )
            ; ( Identifier.Ctor.Ctor "C"
              , [ ( Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T")
                  , Variance.inv
                  , Ty.Param_bounds.create
                      ~lower_bound:Ty.(ctor (ctor_nm "Small") [])
                      ~upper_bound:Ty.(ctor (ctor_nm "Bigly") [])
                      () )
                ]
              , [ (ctor_nm "ICovContrav", Ty.[ generic (ty_param_nm "T"); generic (ty_param_nm "T") ]) ] )
            ])
      in
      let small = Ty.ctor (ctor_nm "Small") []
      and bigly = Ty.ctor (ctor_nm "Bigly") [] in
      let t_scrut = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Tscrut") in
      let t_scrut_bounds = Ty.Param_bounds.top in
      let t_test = Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ttest") in
      let t_test_bounds = Ty.Param_bounds.create ~lower_bound:small ~upper_bound:bigly () in
      let ty_param = Envir.Ty_param.(bind (bind empty t_scrut t_scrut_bounds) t_test t_test_bounds) in
      let ty_param_refine = Envir.Ty_param_refine.empty in
      let ctxt = Refinement.Ctxt.create ~ty_param ~ty_param_refine ~oracle () in
      (* Scrutinee and test type *)
      let ty_scrut = Ty.ctor (ctor_nm "ICovContrav") Ty.[ Generic t_scrut; Generic t_scrut ] in
      let ty_test = Ty.ctor (ctor_nm "C") [ Ty.Generic t_test ] in
      (* Expected type parameter refinement *)
      let expect =
        let bnds_scrut =
          Ty.Param_bounds.create ~lower_bound:Ty.(union [ small; small ]) ~upper_bound:Ty.(inter [ bigly; bigly ]) ()
        in
        let bnds_test =
          let ty_t_scrut = Ty.Generic t_scrut in
          Ty.Param_bounds.create
            ~lower_bound:Ty.(union [ ty_t_scrut; ty_t_scrut ])
            ~upper_bound:Ty.(inter [ ty_t_scrut; ty_t_scrut ])
            ()
        in
        Ok Envir.Ty_param_refine.(bounds @@ Ty.Generic.Map.of_alist_exn [ t_scrut, bnds_scrut; t_test, bnds_test ])
      in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T>\nclass A implements I<Four> {}\nI<Ta> ↓ A = { nothing <= Ta <= Four }\n"
          (Refinement.refine ~ty_scrut ~ty_test ~ctxt)
          expect
      in
      Alcotest.test_case "refinement / nested / hack comparison case 2" `Quick test
    ;;

    let test_cases = [ case_1; case_2; case_3 ]
  end

  let test_cases =
    List.concat
      [ Gadt_covariant.test_cases
      ; Invariant_class_impl_covariant.test_cases
      ; Non_generic_class_impl_covariant.test_cases
      ; Nested.test_cases
      ; Union.test_cases
      ; Intersection.test_cases
      ; Hack_comparison.test_cases
      ]
  ;;
end

let test_cases = List.concat [ Down.test_cases ]
