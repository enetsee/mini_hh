let synth t =
  let def_ctxt = Ctxt.Def.empty
  and cont_ctxt = Ctxt.Cont.empty in
  match t with
  | Lang.Def.Fn fn_def -> Fn_def.synth fn_def ~def_ctxt ~cont_ctxt
  | Lang.Def.Classish classish_def -> Classish_def.synth classish_def ~def_ctxt ~cont_ctxt
;;
