open Core

module Minimal = struct
  type t =
    { line : int
    ; bol : int
    ; offset : int
    }
  [@@deriving create, equal, fields, sexp, yojson]

  let pp ppf { line; bol; offset } = Fmt.(vbox @@ pair ~sep:(any ":") int int) ppf (line, offset - bol)
end

include Minimal
include Pretty.Make (Minimal)

let compare { line = line1; bol = bol1; offset = offset1 } { line = line2; bol = bol2; offset = offset2 } =
  let c = Int.compare line1 line2 in
  if c <> 0 then c else Int.compare (offset1 + bol1) (offset2 + bol2)
;;

let min t1 t2 =
  let c = compare t1 t2 in
  if c > 0 then t2 else t1
;;

let max t1 t2 =
  let c = compare t1 t2 in
  if c < 0 then t2 else t1
;;

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
