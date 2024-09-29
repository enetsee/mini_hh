open Core

type t =
  { line : int
  ; bol : int
  ; offset : int
  }
[@@deriving compare, create, equal, fields, sexp, show, yojson]

let empty = { line = 0; bol = 0; offset = 0 }
let is_empty { line; bol; offset } = line = 0 && bol = 0 && offset = 0
let beg_of_file = { line = 1; bol = 0; offset = 0 }
let set_column_unchecked t c = { t with offset = t.offset + c }
let set_column t c = Some (set_column_unchecked t c)
let column t = offset t - bol t
let line_beg t = line t, bol t
let line_column t = line t, column t
let line_column_offset t = line t, column t, offset t
let line_beg_offset t = line t, bol t, offset t
