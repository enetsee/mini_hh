open Core
open Reporting
open Common

(* We can always synthesize a type for a literal *)
let synth (lit, span) =
  match lit with
  | Lit.Bool _ -> Ty.bool @@ Prov.lit_bool span
  | Lit.Lnum _ -> Ty.int @@ Prov.lit_lnum span
  | Lit.Dnum _ -> Ty.float @@ Prov.lit_dnum span
  | Lit.Const_string _ -> Ty.string @@ Prov.lit_const_string span
  | Lit.Null -> Ty.null @@ Prov.lit_null span
;;

let check lit ~against ~ctxt_cont =
  (* Subsumption case - sythesize a type (`ty`) then generate the subtype constraint  `ty <: against` *)
  let ty_sub = synth lit in
  let subty_err_opt =
    Subtyping.Tell.is_subtype ~ty_sub ~ty_super:against ~ctxt_cont
  in
  let _ : unit =
    Option.iter subty_err_opt ~f:(fun err -> Eff.log_error (Err.subtyping err))
  in
  ()
;;
