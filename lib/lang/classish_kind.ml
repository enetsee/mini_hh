open Core
open Reporting

type t =
  | Class of
      { is_abstract : Span.t option
      ; is_final : Span.t option
      }
  | Intf
  | Trait
[@@deriving eq, compare, sexp, show, variants]
