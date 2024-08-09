open Test_common
open Common

module Classish = struct
  module Up = struct
    let result = Alcotest.option @@ Alcotest.pair (Alcotest.list Testable.ty) Testable.param_bounds

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
      let expect = Some ([ Ty.int ], Ty.Generic.Map.empty) in
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
      let expect = Some ([ Ty.int; Ty.bool ], Ty.Generic.Map.empty) in
      let test () =
        Alcotest.check
          result
          "\ninterface I<T1,T2>\nclass A<T> extends I<int,T> {}\nA<bool> ↑ I = I<int,bool>\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / concrete super 2" `Quick test
    ;;

    let bounds_1 =
      let bounds = Ty.Param_bounds.create ~lower_bound:Ty.int ~upper_bound:Ty.(union [ int; string ]) () in
      let oracle =
        Oracle.(
          add_classishes_exn
            empty
            [ ( Identifier.Ctor.Ctor "I"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, Ty.Param_bounds.top ]
              , [] )
            ; ( Identifier.Ctor.Ctor "A"
              , [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "T"), Variance.inv, bounds ]
              , [ Identifier.Ctor.Ctor "I", [ Ty.generic @@ Identifier.Ty_param.Ty_param "T" ] ] )
            ])
      in
      let ta = Ty.generic @@ Identifier.Ty_param.Ty_param "Ta" in
      let of_ = Ty.Ctor.{ ctor = Identifier.Ctor.(Ctor "A"); args = [ ta ] } in
      let at = Identifier.Ctor.Ctor "I" in
      let expect =
        Some ([ ta ], Ty.Generic.Map.of_alist_exn [ Ty.Generic.Generic (Identifier.Ty_param.Ty_param "Ta"), bounds ])
      in
      let test () =
        Alcotest.check
          result
          "interface I<T>\nclass A<T super int as arraykey> extends I<T> {}\nA<Ta> ↑ I = I<Ta>, int <: Ta <: arraykey\n"
          (Oracle.up oracle ~of_ ~at)
          expect
      in
      Alcotest.test_case "classish / up / concrete super 2" `Quick test
    ;;

    let test_cases = [ concrete_super_1; concrete_super_2; bounds_1 ]
  end

  let test_cases = List.concat [ Up.test_cases ]
end

let test_cases = List.concat [ Classish.test_cases ]
