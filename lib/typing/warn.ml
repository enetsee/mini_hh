open Core
open Reporting

type t =
  | Unreachable of
      { span_return : Span.t option
      ; span_dead : Span.t
      }
  | Impossible_refinement of Subtyping.Err.t
[@@deriving compare, eq, sexp, show, variants]
