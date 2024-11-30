open Core

type 'a t =
  | Empty
  | Step of
      { left : 'a Memo_tree.t list
      ; up : 'a t
      ; right : 'a Memo_tree.t list
      }
[@@deriving compare, equal, map, sexp, variants]
