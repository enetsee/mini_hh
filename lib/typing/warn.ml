open Core
open Reporting

type t =
  | Unreachable of
      { span_return : Span.t option
      ; span_dead : Span.t
      }
  | Impossible_refinement of Subtyping.Err.t
[@@deriving compare, eq, sexp, show, variants]

let to_string = function
  | Unreachable { span_return; span_dead } ->
    Format.sprintf
      {|Unreachable code: this return statement %s means this code can never be reached %s|}
      (Span.to_string @@ Option.value ~default:Span.empty span_return)
      (Span.to_string span_dead)
  | Impossible_refinement err ->
    Format.sprintf
      {|Impossible refinement: this refinement will never be true (%s)|}
      (Subtyping.Err.to_string err)
;;
