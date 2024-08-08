open Core

module type S = sig
  module Elem : Elem.S
  module Lit : Lit.S with module Elem := Elem

  (** A clause is a non-empty conjunction of literals *)
  type t [@@deriving compare, sexp, show]

  val pos : Elem.t -> t
  val neg : Elem.t -> t
  val of_lists : pos:Elem.t list -> neg:Elem.t list -> t
  val to_lists : t -> Elem.t list * Elem.t list
  val meet : t -> t -> t
  val cmp : t -> t
end

module Make (Elem : Elem.S) (Lit : Lit.S with module Elem := Elem) : S with module Elem := Elem and module Lit := Lit =
struct
  include Set.Make (Lit)

  let pp ppf t = Fmt.(hovbox @@ list ~sep:(any "∧") Lit.pp) ppf @@ Set.to_list t
  let show = Fmt.to_to_string pp
  let pos elem = singleton (Lit.pos elem)
  let neg elem = singleton (Lit.neg elem)

  let of_lists ~pos ~neg =
    let poss = List.map ~f:Lit.pos pos
    and negs = List.map ~f:Lit.neg neg in
    Set.union (of_list poss) (of_list negs)
  ;;

  (** The meet (or greatest lower bound or intersection )*)
  let meet t1 t2 = Set.union t1 t2

  (** Since we assume the set is not empty we can define the complemenent *)
  let cmp t = map t ~f:Lit.cmp

  let to_lists t = List.partition_map ~f:Lit.to_either @@ Set.to_list t
end
