open Core

let synth Lang.Prog.{ defs } = List.iter ~f:Def.synth defs
