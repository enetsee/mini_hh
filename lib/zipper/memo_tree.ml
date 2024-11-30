open Core

type 'a t =
  | Leaf of 'a
  | Branch of 'a Tree.t list
  | Branch_scar of
      { left : 'a t list
      ; focus : 'a t
      ; right : 'a t list
      }
[@@deriving compare, eq, map, sexp, variants]

let of_tree t =
  match t with
  | Tree.Leaf a -> Leaf a
  | Tree.Branch ts -> Branch ts
;;

let rec to_tree = function
  | Leaf x -> Tree.leaf x
  | Branch xs -> Tree.branch xs
  | Branch_scar { left; focus; right } ->
    let left = List.rev @@ List.map ~f:to_tree left
    and x = to_tree focus
    and right = List.map ~f:to_tree right in
    Tree.branch (left @ (x :: right))
;;
