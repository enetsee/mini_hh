open Core

module type S = sig
  module Elem : Elem.S

  type t [@@deriving compare, equal, sexp, show]

  val pos : Elem.t -> t
  val neg : Elem.t -> t
  val is_pos : t -> bool
  val is_neg : t -> bool
  val pos_val : t -> Elem.t option
  val neg_val : t -> Elem.t option
  val cmp : t -> t
  val to_either : t -> (Elem.t, Elem.t) Either.t
end

module Make (Elem : Elem.S) : S with module Elem := Elem = struct
  type t =
    | Pos of Elem.t
    | Neg of Elem.t
  [@@deriving compare, equal, sexp, variants]

  let pp ppf = function
    | Pos elem -> Elem.pp ppf elem
    | Neg elem -> Fmt.(hbox @@ (any "~" ++ Elem.pp)) ppf elem
  ;;

  let show = Fmt.to_to_string pp

  let cmp t =
    match t with
    | Pos elem -> Neg elem
    | Neg elem -> Pos elem
  ;;

  let to_either = function
    | Pos elem -> Either.First elem
    | Neg elem -> Either.Second elem
  ;;
end
