open Core
open Reporting

type t =
  | Not_a_subtype of
      { prov_sub : Prov.t
      ; prov_super : Prov.t
      }
  | Disj of t list
  | Conj of t list
  | Multiple of t list
[@@deriving compare, eq, sexp, show, variants]
