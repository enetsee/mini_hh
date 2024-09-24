module Fn = struct
  type t = { ret_ty : Ty.t } [@@deriving create, show]
end

type t =
  { oracle : Oracle.t
  ; class_ : Name.Ctor.t option
  ; fn : Fn.t option
  }
[@@deriving create, show]
