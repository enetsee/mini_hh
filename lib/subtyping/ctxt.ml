type t =
  { ty_param : Ty.Param.Ctxt.t
  ; ty_param_refine : Ty.Param.Refinement.t
  ; oracle : Oracle.t
  }
[@@deriving create, show]
