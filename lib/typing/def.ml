let synth t =
  let def_ctxt = Ctxt.Def.empty
  and ctxt_cont = Ctxt.Cont.empty in
  match t with
  | Lang.Def.Fn fn_def -> Fn_def.synth fn_def ~def_ctxt ~ctxt_cont
  | Lang.Def.Classish classish_def ->
    Classish_def.synth classish_def ~def_ctxt ~ctxt_cont
  | Lang.Def.Ty _ -> ()
;;
