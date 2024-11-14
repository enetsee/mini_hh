open Core

let option pp equal = Alcotest.testable Fmt.(option pp) @@ Option.equal equal

let tuple (pp1, equal1) (pp2, equal2) =
  Alcotest.testable Fmt.(hovbox @@ pair ~sep:sp pp1 pp2)
  @@ Tuple2.equal ~eq1:equal1 ~eq2:equal2
;;

let ty = Alcotest.testable Ty.pp Ty.equal

let ty_param_refine =
  Alcotest.testable Ctxt.Ty_param.Refinement.pp Ctxt.Ty_param.Refinement.equal
;;

let refinement = Alcotest.testable Ty.Refinement.pp Ty.Refinement.equal
let subtyping_err = Alcotest.testable Subtyping.Err.pp Subtyping.Err.equal
let prov = Alcotest.testable Reporting.Prov.pp Reporting.Prov.equal
