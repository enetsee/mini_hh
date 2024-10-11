open Reporting

type t =
  | Fn of Fn_def.t Located.t
  | Classish of Classish_def.t Located.t
[@@deriving compare, eq, sexp, show, variants]
