open Core
open Reporting
open Common

type t =
  { name : Name.Ty_param.t Located.t
  ; variance : Variance.t Located.t
  ; bounds : Ty_param_bound_def.t Located.t list
  }
[@@deriving compare, create, eq, sexp, show]
