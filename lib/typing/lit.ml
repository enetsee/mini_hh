open Core
open Reporting
open Common

(* We can always synthesize a type for a literal *)
let synth (lit, span) =
  let delta =
    let rfmts = Some Ctxt.Cont.Refinements.empty in
    Ctxt.Cont.Expr_delta.{ empty with rfmts }
  in
  match lit with
  | Lit.Bool b ->
    ( Ty.bool @@ Prov.lit_bool span
    , if b then delta else Ctxt.Cont.Expr_delta.empty )
  | Lit.Lnum _ -> Ty.int @@ Prov.lit_lnum span, delta
  | Lit.Dnum _ -> Ty.float @@ Prov.lit_dnum span, delta
  | Lit.Const_string _ -> Ty.string @@ Prov.lit_const_string span, delta
  | Lit.Null -> Ty.null @@ Prov.lit_null span, delta
;;

let check lit ~against ~ctxt_cont =
  (* Subsumption case - sythesize a type (`ty`) then generate the subtype constraint  `ty <: against` *)
  let ty_sub, delta = synth lit in
  let subty_err_opt =
    Subtyping.Tell.is_subtype ~ty_sub ~ty_super:against ~ctxt_cont
  in
  let _ : unit =
    Option.iter subty_err_opt ~f:(fun err -> Eff.log_error (Err.subtyping err))
  in
  ty_sub, delta
;;
