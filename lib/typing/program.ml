open Core

let synth defs =
  let def_ctxt = Ctxt.Def.empty
  and cont_ctxt = Ctxt.Cont.empty in
  List.map defs ~f:(fun def ->
    match def with
    | Lang.Def.Fn fn_def -> Fn_def.synth fn_def ~def_ctxt ~cont_ctxt
    | Lang.Def.Classish classish_def -> Classish_def.synth classish_def ~def_ctxt ~cont_ctxt)
;;
