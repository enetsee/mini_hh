open Core

module type S = sig
  module Elem : Elem.S
  module Lit : Lit.S with module Elem := Elem
  module Clause : Clause.S with module Elem := Elem and module Lit := Lit

  (** A disjunction of clauses *)
  type t [@@deriving compare, eq, sexp, show]

  val bottom : t
  val empty : t
  val is_bottom : t -> bool
  val singleton : Clause.t -> t
  val of_list : Clause.t list -> t
  val to_list : t -> Clause.t list
  val meet : t -> t -> t
  val join : t -> t -> t
end

module Make
    (Elem : Elem.S)
    (Lit : Lit.S with module Elem := Elem)
    (Clause : Clause.S with module Elem := Elem and module Lit := Lit) :
  S with module Elem := Elem and module Lit := Lit and module Clause := Clause = struct
  include Set.Make (Clause)

  let pp ppf t = Fmt.(hovbox @@ list ~sep:(any "∨") @@ parens Clause.pp) ppf @@ Set.to_list t
  let show = Fmt.to_to_string pp

  let meet t1 t2 =
    of_list
    @@ List.concat_map (Set.elements t1) ~f:(fun c1 -> List.map ~f:(fun c2 -> Clause.meet c1 c2) @@ Set.elements t2)
  ;;

  let to_list t = Set.to_list t
  let join t1 t2 = Set.union t1 t2
  let bottom = empty
  let is_bottom t = Set.is_empty t
end
