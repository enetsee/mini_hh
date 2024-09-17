open Core

type t = Bool of bool [@@deriving eq, show, compare, sexp, variants]
