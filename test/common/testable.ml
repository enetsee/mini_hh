open Core

let option pp equal = Alcotest.testable Fmt.(option pp) @@ Option.equal equal

let tuple (pp1, equal1) (pp2, equal2) =
  Alcotest.testable Fmt.(hovbox @@ pair ~sep:sp pp1 pp2) @@ Tuple2.equal ~eq1:equal1 ~eq2:equal2
;;

let ty = Alcotest.testable Ty.pp Ty.equal
let ty_list = Alcotest.testable Fmt.(hovbox @@ brackets @@ list ~sep:comma Ty.pp) (List.equal Ty.equal)
let param_bounds = Alcotest.testable Ty.(Generic.Map.pp Param_bounds.pp) Ty.(Generic.Map.equal Param_bounds.equal)
