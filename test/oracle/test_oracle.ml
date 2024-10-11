(* open Test_common
open Common
open Reporting

module Classish = struct
  module Up = struct
    let result = Alcotest.option @@ Alcotest.list Testable.ty

    let concrete_super_1 =
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Name.Ctor.of_string "I"
              , [ Name.Ty_param.of_string "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ]
              , [] )
            ; Name.Ctor.of_string "A", [], [ Name.Ctor.of_string "I", [ Ty.int Prov.empty ] ]
            ])
      in
      let of_ = Ty.Ctor.create ~name:Name.Ctor.(of_string "A") () in
      let at = Name.Ctor.of_string "I" in
      let expect = Some [ Ty.int Prov.empty ] in
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
            [ ( Name.Ctor.of_string "I"
              , [ Name.Ty_param.of_string "T1", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ]
              , [] )
            ; ( Name.Ctor.of_string "A"
              , [ Name.Ty_param.of_string "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ]
              , [ Name.Ctor.of_string "I", [ Ty.int Prov.empty; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T" ] ]
              )
            ])
      in
      let of_ = Ty.Ctor.create ~name:Name.Ctor.(of_string "A") ~args:[ Ty.bool Prov.empty ] () in
      let at = Name.Ctor.of_string "I" in
      let expect = Some [ Ty.int Prov.empty; Ty.bool Prov.empty ] in
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
      let bounds =
        Ty.Param_bounds.create
          ~lower:Ty.(int Prov.empty)
          ~upper:Ty.(union [ int Prov.empty; string Prov.empty ] ~prov:Prov.empty)
          ()
      in
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ (* interface I<T> {} *)
              ( Name.Ctor.of_string "I"
              , [ Name.Ty_param.of_string "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ]
              , [] )
              (* class A<T super int as arraykey> implements I<T> {} *)
            ; ( Name.Ctor.of_string "A"
              , [ Name.Ty_param.of_string "T", Variance.inv, bounds, Span.empty ]
              , [ Name.Ctor.of_string "I", [ Ty.generic Prov.empty @@ Name.Ty_param.of_string "T" ] ] )
            ])
      in
      let ta = Ty.generic Prov.empty @@ Name.Ty_param.of_string "Ta" in
      let of_ = Ty.Ctor.{ name = Name.Ctor.(Ctor "A"); args = [ ta ] } in
      let at = Name.Ctor.of_string "I" in
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
            [ ( Name.Ctor.of_string "I"
              , [ Name.Ty_param.of_string "T1", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ]
              , [ ( Name.Ctor.of_string "J"
                  , [ Ty.generic Prov.empty @@ Name.Ty_param.of_string "T1"
                    ; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T2"
                    ] )
                ] )
            ; ( Name.Ctor.of_string "J"
              , [ Name.Ty_param.of_string "T1", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ]
              , [] )
            ; ( Name.Ctor.of_string "A"
              , [ Name.Ty_param.of_string "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ]
              , [ Name.Ctor.of_string "I", [ Ty.int Prov.empty; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T" ] ]
              )
            ])
      in
      let of_ = Ty.Ctor.{ name = Name.Ctor.(Ctor "A"); args = [ Ty.bool Prov.empty ] } in
      let at = Name.Ctor.of_string "J" in
      let expect = Some [ Ty.int Prov.empty; Ty.bool Prov.empty ] in
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
            [ ( Name.Ctor.of_string "I"
              , [ Name.Ty_param.of_string "T1", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ]
              , [ ( Name.Ctor.of_string "J"
                  , [ Ty.generic Prov.empty @@ Name.Ty_param.of_string "T1"
                    ; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T2"
                    ; Ty.int Prov.empty
                    ] )
                ] )
            ; ( Name.Ctor.of_string "J"
              , [ Name.Ty_param.of_string "T1", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ]
              , [] )
            ; ( Name.Ctor.of_string "A"
              , [ Name.Ty_param.of_string "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ]
              , [ Name.Ctor.of_string "I", [ Ty.int Prov.empty; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T" ] ]
              )
            ])
      in
      let of_ = Ty.Ctor.{ name = Name.Ctor.(Ctor "A"); args = [ Ty.bool Prov.empty ] } in
      let at = Name.Ctor.of_string "J" in
      let expect = Some [ Ty.int Prov.empty; Ty.bool Prov.empty; Ty.int Prov.empty ] in
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
      let bounds =
        Ty.Param_bounds.create
          ~lower:(Ty.int Prov.empty)
          ~upper:Ty.(union [ int Prov.empty; string Prov.empty ] ~prov:Prov.empty)
          ()
      in
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ (* interface J<T1,T2> {} *)
              ( Name.Ctor.of_string "J"
              , [ Name.Ty_param.of_string "T1", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ]
              , [] )
            ; (* interface I<T> extends J<int,T> {} *)
              ( Name.Ctor.of_string "I"
              , [ Name.Ty_param.of_string "T", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty ]
              , [ Name.Ctor.of_string "J", [ Ty.int Prov.empty; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T" ] ]
              )
              (* class A<T super int as arraykey> implements I<T> {} *)
            ; ( Name.Ctor.of_string "A"
              , [ Name.Ty_param.of_string "T", Variance.inv, bounds, Span.empty ]
              , [ Name.Ctor.of_string "I", [ Ty.generic Prov.empty @@ Name.Ty_param.of_string "T" ] ] )
            ])
      in
      let ta = Ty.generic Prov.empty @@ Name.Ty_param.of_string "Ta" in
      let of_ = Ty.Ctor.{ name = Name.Ctor.(Ctor "A"); args = [ ta ] } in
      let at = Name.Ctor.of_string "J" in
      let expect = Some [ Ty.int Prov.empty; ta ] in
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
      let bounds_t1 = Ty.Param_bounds.create ~lower:(Ty.int Prov.empty) ~upper:(Ty.arraykey Prov.empty) () in
      let bounds_t2 = Ty.Param_bounds.create ~lower:(Ty.nothing Prov.empty) ~upper:(Ty.arraykey Prov.empty) () in
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Name.Ctor.of_string "J"
              , [ Name.Ty_param.of_string "T1", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T3", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ]
              , [] )
            ; ( Name.Ctor.of_string "I"
              , [ Name.Ty_param.of_string "T1", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ; Name.Ty_param.of_string "T3", Variance.inv, Ty.Param_bounds.top Prov.empty, Span.empty
                ]
              , [ ( Name.Ctor.of_string "J"
                  , [ Ty.generic Prov.empty @@ Name.Ty_param.of_string "T3"
                    ; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T2"
                    ; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T1"
                    ] )
                ] )
            ; ( Name.Ctor.of_string "A"
              , [ Name.Ty_param.of_string "T1", Variance.inv, bounds_t1, Span.empty
                ; Name.Ty_param.of_string "T2", Variance.inv, bounds_t2, Span.empty
                ]
              , [ ( Name.Ctor.of_string "I"
                  , [ Ty.generic Prov.empty @@ Name.Ty_param.of_string "T2"
                    ; Ty.bool Prov.empty
                    ; Ty.generic Prov.empty @@ Name.Ty_param.of_string "T1"
                    ] )
                ] )
            ])
      in
      let ta = Ty.generic Prov.empty @@ Name.Ty_param.of_string "Ta" in
      let tb = Ty.generic Prov.empty @@ Name.Ty_param.of_string "Tb" in
      let of_ = Ty.Ctor.{ name = Name.Ctor.(Ctor "A"); args = [ ta; tb ] } in
      let at = Name.Ctor.of_string "J" in
      let expect = Some [ ta; Ty.bool Prov.empty; tb ] in
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
              ( Name.Ctor.of_string "I"
              , [  (Name.Ty_param.of_string "T"), Variance.inv, Ty.Param_bounds.top ]
              , [] )
            ; (* class A implements I<arraykey> {} *)
              Name.Ctor.of_string "A", [], [ Name.Ctor.of_string "I", [ Ty.arraykey ] ]
            ; (* class B implements I<string> {} *)
              Name.Ctor.of_string "B", [], [ Name.Ctor.of_string "I", [ Ty.string ] ]
            ; (* class C extends A, B {} *)
              Name.Ctor.of_string "C", [], [ Name.Ctor.of_string "A", []; Name.Ctor.of_string "B", [] ]
            ])
      in
      let of_ = Ty.Ctor.{ name =Name.Ctor.(Ctor "C"); args = [] } in
      let at = Name.Ctor.of_string "I" in
      let expect = Some ([ Ty.(inter [ arraykey; string ]) ], Name.Ty_param.of_string.empty) in
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

let test_cases = List.concat [ Classish.test_cases ] *)
