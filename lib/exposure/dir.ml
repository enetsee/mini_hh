type t =
  | Up
  | Down

let flip = function
  | Up -> Down
  | Down -> Up
;;

let is_up = function
  | Up -> true
  | _ -> false
;;
