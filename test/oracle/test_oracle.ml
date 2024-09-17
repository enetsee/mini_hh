open Test_common
open Common

module Classish = struct
  module Up = struct
    let result = Alcotest.option @@ Alcotest.list Testable.ty

    let concrete_super_1 =
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [] )
            ; Identifier.Ctor.Ctor "A", [], [ Identifier.Ctor.Ctor "I", [ Ty.int ] ]
            ])
      in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "A"); args = [] } in
      let at = Identifier.Ctor.Ctor "I" in
      let expect = Some [ Ty.int ] in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T1>\nclass A extends I<int> {}\nA ↑ I = I<int>\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / concrete super 1" `Quick test
    ;;

    let concrete_super_2 =
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
              , [] )
            ; ( Identifier.Ctor.Ctor "A"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [ Identifier.Ctor.Ctor "I", [ Ty.int; Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ] )
            ])
      in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "A"); args = [ Ty.bool ] } in
      let at = Identifier.Ctor.Ctor "I" in
      let expect = Some [ Ty.int; Ty.bool ] in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T1,T2>\nclass A<T> extends I<int,T> {}\nA<bool> ↑ I = I<int,bool>\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / concrete super 2" `Quick test
    ;;

    (**
       interface I<T> {}
       class A<T super int as arrayey> implements I<T> {}
       A<Ta> up I
     *)
    let bounds_1 =
      let bounds = Ty.Param_bounds.create ~lower_bound:Ty.int ~upper_bound:Ty.(union [ int; string ]) () in
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ (* interface I<T> {} *)
              ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [] )
              (* class A<T super int as arraykey> implements I<T> {} *)
            ; ( Identifier.Ctor.Ctor "A"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, bounds ]
              , [ Identifier.Ctor.Ctor "I", [ Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ] )
            ])
      in
      let ta = Ty.generic @@ Identifier.Ty_param.Ty_param "Ta" in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "A"); args = [ ta ] } in
      let at = Identifier.Ctor.Ctor "I" in
      let expect = Some [ ta ] in
      let test () =
        Alcotest.check
          result
          "interface I<T>\nclass A<T super int as arraykey> extends I<T> {}\nA<Ta> ↑ I = I<Ta>, int <: Ta <: arraykey\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / bounds 1" `Quick test
    ;;

    let transitive_super_1 =
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
              , [ ( Identifier.Ctor.Ctor "J"
                  , [ Ty.generic @@ Identifier.Ty_param.Ty_param "T1"; Ty.generic @@ Identifier.Ty_param.Ty_param "T2" ]
                  )
                ] )
            ; ( Identifier.Ctor.Ctor "J"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
              , [] )
            ; ( Identifier.Ctor.Ctor "A"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [ Identifier.Ctor.Ctor "I", [ Ty.int; Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ] )
            ])
      in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "A"); args = [ Ty.bool ] } in
      let at = Identifier.Ctor.Ctor "J" in
      let expect = Some [ Ty.int; Ty.bool ] in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T1,T2>\ninterface J<T1,T2>\nclass A<T> extends I<int,T> {}\nA<bool> ↑ J = J<int,bool>\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / transitive super 1" `Quick test
    ;;

    let transitive_super_2 =
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
              , [ ( Identifier.Ctor.Ctor "J"
                  , [ Ty.generic @@ Identifier.Ty_param.Ty_param "T1"
                    ; Ty.generic @@ Identifier.Ty_param.Ty_param "T2"
                    ; Ty.int
                    ] )
                ] )
            ; ( Identifier.Ctor.Ctor "J"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
              , [] )
            ; ( Identifier.Ctor.Ctor "A"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [ Identifier.Ctor.Ctor "I", [ Ty.int; Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ] )
            ])
      in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "A"); args = [ Ty.bool ] } in
      let at = Identifier.Ctor.Ctor "J" in
      let expect = Some [ Ty.int; Ty.bool; Ty.int ] in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T1,T2>\ninterface J<T1,T2>\nclass A<T> extends I<int,T> {}\nA<bool> ↑ J = J<int,bool>\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / transitive super 2" `Quick test
    ;;

    (**
       interface J<T1,T2> {}
       interface I<T> extends J<int,T> {}
       class A<T super int as arrayey> implements I<T> {}
       A<Ta> up J
    *)
    let transitive_bounds_1 =
      let bounds = Ty.Param_bounds.create ~lower_bound:Ty.int ~upper_bound:Ty.(union [ int; string ]) () in
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ (* interface J<T1,T2> {} *)
              ( Identifier.Ctor.Ctor "J"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ]
              , [] )
            ; (* interface I<T> extends J<int,T> {} *)
              ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [ Identifier.Ctor.Ctor "J", [ Ty.int; Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ] )
              (* class A<T super int as arraykey> implements I<T> {} *)
            ; ( Identifier.Ctor.Ctor "A"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, bounds ]
              , [ Identifier.Ctor.Ctor "I", [ Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ] )
            ])
      in
      let ta = Ty.generic @@ Identifier.Ty_param.Ty_param "Ta" in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "A"); args = [ ta ] } in
      let at = Identifier.Ctor.Ctor "J" in
      let expect = Some [ Ty.int; ta ] in
      let test () =
        Alcotest.check
          result
          "interface J<T1,T2>\n\
           interface I<T> extensd J<int,T2>\n\
           class A<T super int as arraykey> extends I<T> {}\n\
           A<Ta> ↑ J = J<int,Ta>, int <: Ta <: arraykey\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / transitive bounds 1" `Quick test
    ;;

    (**
       interface J<T,T2> {}
       interface I<T1,T2> extends J<T2,T1> {}
       class A<T1 super int as arraykey, T2 as arraykey> implements I<T2,T1> {}
       A<Ta> up J
    *)
    let transitive_bounds_2 =
      let bounds_t1 = Ty.Param_bounds.create ~lower_bound:Ty.int ~upper_bound:Ty.arraykey () in
      let bounds_t2 = Ty.Param_bounds.create ~upper_bound:Ty.arraykey () in
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Identifier.Ctor.Ctor "J"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T3"), Variance.inv, Ty.Param_bounds.top
                ]
              , [] )
            ; ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, Ty.Param_bounds.top
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T3"), Variance.inv, Ty.Param_bounds.top
                ]
              , [ ( Identifier.Ctor.Ctor "J"
                  , [ Ty.generic @@ Identifier.Ty_param.Ty_param "T3"
                    ; Ty.generic @@ Identifier.Ty_param.Ty_param "T2"
                    ; Ty.generic @@ Identifier.Ty_param.Ty_param "T1"
                    ] )
                ] )
            ; ( Identifier.Ctor.Ctor "A"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T1"), Variance.inv, bounds_t1
                ; Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T2"), Variance.inv, bounds_t2
                ]
              , [ ( Identifier.Ctor.Ctor "I"
                  , [ Ty.generic @@ Identifier.Ty_param.Ty_param "T2"
                    ; Ty.bool
                    ; Ty.generic @@ Identifier.Ty_param.Ty_param "T1"
                    ] )
                ] )
            ])
      in
      let ta = Ty.generic @@ Identifier.Ty_param.Ty_param "Ta" in
      let tb = Ty.generic @@ Identifier.Ty_param.Ty_param "Tb" in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "A"); args = [ ta; tb ] } in
      let at = Identifier.Ctor.Ctor "J" in
      let expect = Some [ ta; Ty.bool; tb ] in
      let test () =
        Alcotest.check
          result
          "interface J<T1,T2>\n\
           interface I<T> extensd J<int,T2>\n\
           class A<T super int as arraykey> extends I<T> {}\n\
           A<Ta> ↑ J = J<int,Ta>, int <: Ta <: arraykey\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / transitive bounds 2" `Quick test
    ;;

    (**
       interface I<T> {}
       class A implements I<arraykey> {}
       class B implements I<string> {}
       class C extends A, B {}
       A up I
    *)
    (* let multiple_instantiation =
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ (* interface I<T> {} *)
              ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [] )
            ; (* class A implements I<arraykey> {} *)
              Identifier.Ctor.Ctor "A", [], [ Identifier.Ctor.Ctor "I", [ Ty.arraykey ] ]
            ; (* class B implements I<string> {} *)
              Identifier.Ctor.Ctor "B", [], [ Identifier.Ctor.Ctor "I", [ Ty.string ] ]
            ; (* class C extends A, B {} *)
              Identifier.Ctor.Ctor "C", [], [ Identifier.Ctor.Ctor "A", []; Identifier.Ctor.Ctor "B", [] ]
            ])
      in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "C"); args = [] } in
      let at = Identifier.Ctor.Ctor "I" in
      let expect = Some ([ Ty.(inter [ arraykey; string ]) ], Ty.Generic.Map.empty) in
      let test () =
        Alcotest.check
          result
          "interface I<T> {}\n\
           class A implements I<arraykey> {}\n\
           class B implements I<string> {}\n\
           class C extends A, B {}\n\
           C ↑ I = I<arraykey & string>, {}\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / multiple instantiation" `Quick test
    ;; *)

    let test_cases =
      [ concrete_super_1
      ; concrete_super_2
      ; bounds_1
      ; transitive_super_1
      ; transitive_super_2
      ; transitive_bounds_1
      ; transitive_bounds_2 (* ; multiple_instantiation *)
      ]
    ;;
  end

  let test_cases = List.concat [ Up.test_cases ]
end

let test_cases = List.concat [ Classish.test_cases ]
