open Core

type t =
  { line : int
  ; beg_of_line : int
  ; offset : int
  }
[@@deriving compare, create, equal, fields, sexp, show, yojson]

let empty = { line = 0; beg_of_line = 0; offset = 0 }
let is_empty { line; beg_of_line; offset } = line = 0 && beg_of_line = 0 && offset = 0
let beg_of_file = { line = 1; beg_of_line = 0; offset = 0 }
let set_column_unchecked t c = { t with offset = t.offset + c }
let set_column t c = Some (set_column_unchecked t c)
let column t = offset t - beg_of_line t
let line_beg t = line t, beg_of_line t
let line_column t = line t, column t
let line_column_offset t = line t, column t, offset t
let line_beg_offset t = line t, beg_of_line t, offset t
