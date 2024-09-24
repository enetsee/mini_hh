open Core

let option pp equal = Alcotest.testable Fmt.(option pp) @@ Option.equal equal

let tuple (pp1, equal1) (pp2, equal2) =
  Alcotest.testable Fmt.(hovbox @@ pair ~sep:sp pp1 pp2) @@ Tuple2.equal ~eq1:equal1 ~eq2:equal2
;;

let ty = Alcotest.testable Ty.pp Ty.equal
let ty_param_refine = Alcotest.testable Envir.Ty_param_refine.pp Envir.Ty_param_refine.equal
let refinement = Alcotest.testable Refinement.pp Refinement.equal
let subtyping_err = Alcotest.testable Subtyping.Err.pp Subtyping.Err.equal
