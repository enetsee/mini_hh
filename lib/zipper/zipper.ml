open Core
module Tree = Tree

type 'a path =
  | Empty
  | Step of
      { left : 'a Memo_tree.t list
      ; up : 'a path
      ; right : 'a Memo_tree.t list
      }
[@@deriving compare, equal, map, sexp, variants]

type 'a t =
  { cursor : 'a Memo_tree.t
  ; path : 'a path
  }
[@@deriving compare, create, eq, map, sexp]

let of_tree t = { cursor = Memo_tree.of_tree t; path = Empty }

let move_up t =
  match t with
  | { path = Empty; _ } -> None
  | { cursor; path = Step { left; up = path; right } } ->
    Some { cursor = Memo_tree.branch_scar ~left ~focus:cursor ~right; path }
;;

let move_down { cursor; path } =
  match cursor with
  | Memo_tree.Leaf _ ->
    (* We can't move down from a leaf *)
    None
  | Memo_tree.Branch ts ->
    (match List.map ~f:Memo_tree.of_tree ts with
     | cursor :: right -> Some { cursor; path = step ~left:[] ~up:path ~right }
     | [] -> None)
  | Memo_tree.Branch_scar { left; focus; right } ->
    Some { cursor = focus; path = step ~left ~up:path ~right }
;;

let move_left { cursor; path } =
  match path with
  | Step { left = prev :: left; up; right } ->
    Some { cursor = prev; path = step ~left ~up ~right:(cursor :: right) }
  | Step _ | Empty -> None
;;

let move_right { cursor; path } =
  match path with
  | Step { left; up; right = next :: right } ->
    Some { cursor = next; path = step ~left:(cursor :: left) ~up ~right }
  | Empty | Step _ -> None
;;
