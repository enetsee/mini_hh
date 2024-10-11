module Lit = struct
  type t =
    | Lnum of Span.t
    | Dnum of Span.t
    | Bool of Span.t
    | Null of Span.t
    | Const_string of Span.t
  [@@deriving compare, eq, sexp, show, variants, yojson]
end

type t =
  | Lit of Lit.t
  | Witness of Span.t
[@@deriving compare, eq, sexp, show, variants, yojson]

let lit_null span = lit (Lit.null span)
let lit_bool span = lit (Lit.bool span)
let lit_lnum span = lit (Lit.lnum span)
let lit_dnum span = lit (Lit.dnum span)
let lit_const_string span = lit (Lit.const_string span)
