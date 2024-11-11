open Core

module Minimal = struct
  type t =
    { start_ : Pos.t
    ; end_ : Pos.t
    }
  [@@deriving compare, create, equal, fields, sexp, yojson]

  let pp ppf { start_; end_ } =
    Fmt.(vbox @@ pair ~sep:(any "-") Pos.pp Pos.pp) ppf (start_, end_)
  ;;
end

include Minimal
include Pretty.Make (Minimal)

module Set = struct
  include Set.Make (Minimal)

  let pp ppf t =
    Fmt.(hovbox @@ braces @@ list ~sep:comma pp) ppf @@ Set.to_list t
  ;;
end

let empty = { start_ = Pos.empty; end_ = Pos.empty }

let join { start_ = s1; end_ = e1 } { start_ = s2; end_ = e2 } =
  { start_ = Pos.min s1 s2; end_ = Pos.max e1 e2 }
;;

let joins = function
  | [] -> empty
  | init :: rest -> List.fold_left rest ~init ~f:join
;;

let meet { start_ = s1; end_ = e1 } { start_ = s2; end_ = e2 } =
  { start_ = Pos.max s1 s2; end_ = Pos.min e1 e2 }
;;

let start_line { start_; _ } = start_.line
