open Core

type t =
  | Lnum of string
  | Dnum of string
  | Bool of bool
  | Const_string of string
  | Null
[@@deriving eq, show, compare, sexp, variants]
