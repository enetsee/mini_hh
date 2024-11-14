open Core
open Reporting

let synth local ~cont_ctxt =
  let prov_tm_var = Prov.expr_tm_var @@ Located.span_of local in
  match Ctxt.Cont.find_local cont_ctxt @@ Located.elem local with
  | Some ty ->
    Ty.map_prov ty ~f:(fun prov_def -> Prov.use ~prov_def ~prov_tm_var)
  | None ->
    let _ : unit =
      let err = Err.unbound_local local in
      Eff.log_error err
    in
    Ty.nothing prov_tm_var
;;
