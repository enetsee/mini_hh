open Reporting

type t =
  | Fn of Fn_def.t Located.t
  | Cls of Class_def.t Located.t
  | Intf of Intf_def.t Located.t
[@@deriving compare, eq, sexp, show, variants]
