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

let to_string = function
  | Class { is_abstract = None; is_final = None } -> "class"
  | Class { is_abstract = _; is_final = None } -> "abstract class"
  | Class { is_abstract = None; is_final = _ } -> "final class"
  | Class { is_abstract = _; is_final = _ } -> "abstract final class"
  | Intf -> "interface"
  | Trait -> "trait"
;;
