type t =
  { ty_param : Envir.Ty_param.t
  ; ty_param_refine : Envir.Ty_param_refine.t
  ; oracle : Oracle.t
  }
[@@deriving create, show]
