open Core
module Elem = Elem

module type S = sig
  module Elem : Elem.S

  type t [@@deriving compare, eq, sexp, show]

  val top : t
  val bottom : t
  val meet : t -> t -> t
  val join : t -> t -> t
  val cmp : t -> t
  val pos : Elem.t -> t
  val neg : Elem.t -> t
  val to_list_opt : t -> (Elem.t list * Elem.t list) list option
end

module Make (Elem : Elem.S) : S with module Elem := Elem = struct
  module Lit = Lit.Make (Elem)
  module Clause = Clause.Make (Elem) (Lit)
  module Disj = Disj.Make (Elem) (Lit) (Clause)

  type t =
    | Top
    | Disj of Disj.t
  [@@deriving compare, eq, sexp]

  let pp ppf = function
    | Top -> Fmt.string ppf "⊤"
    | Disj disj when Disj.is_bottom disj -> Fmt.string ppf "⊥"
    | Disj disj -> Disj.pp ppf disj
  ;;

  let show t = Fmt.to_to_string pp t
  let top = Top
  let bottom = Disj Disj.empty

  let meet t1 t2 =
    match t1, t2 with
    | Top, t | t, Top -> t
    | Disj t1, Disj t2 -> Disj (Disj.meet t1 t2)
  ;;

  let join t1 t2 =
    match t1, t2 with
    | Top, _ | _, Top -> Top
    | Disj t1, Disj t2 -> Disj (Disj.meet t1 t2)
  ;;

  let to_list_opt t =
    match t with
    | Top -> None
    | Disj disj -> Some (List.map ~f:Clause.to_lists @@ Disj.to_list disj)
  ;;

  let pos elem = Disj (Disj.singleton @@ Clause.pos elem)
  let neg elem = Disj (Disj.singleton @@ Clause.neg elem)
  let cmp _ = failwith "TODO"
end
