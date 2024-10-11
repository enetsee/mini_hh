open Core

type t =
  { start_ : Pos.t
  ; end_ : Pos.t
  }
[@@deriving compare, create, equal, fields, sexp, show, yojson]

let empty = { start_ = Pos.empty; end_ = Pos.empty }
let join { start_ = s1; end_ = e1 } { start_ = s2; end_ = e2 } = { start_ = Pos.min s1 s2; end_ = Pos.max e1 e2 }

let joins = function
  | [] -> empty
  | init :: rest -> List.fold_left rest ~init ~f:join
;;
