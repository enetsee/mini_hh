module type Synthesizes = sig
  type t
  type out
  type env_out

  val synth : t -> ctxt:Ctxt.t -> env:Envir.Typing.t -> errs:Err.t list -> out * env_out * Err.t list
end

module type Checks = sig
  type t
  type env_out

  val check : t -> against:Ty.t -> ctxt:Ctxt.t -> env:Envir.Typing.t -> errs:Err.t list -> env_out * Err.t list
end
