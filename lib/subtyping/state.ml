type t =
  { store : Cstr.Store.t
  ; supply : int
  }

let empty = { store = Cstr.Store.empty; supply = 0 }

let add_upper_bound ({ store; _ } as t) ~var ~bound =
  let store = Cstr.Store.add_upper_bound store ~var ~bound in
  { t with store }
;;

let add_lower_bound ({ store; _ } as t) ~var ~bound =
  let store = Cstr.Store.add_lower_bound store ~var ~bound in
  { t with store }
;;

let get_lower_bounds_exn { store; _ } ~var =
  Cstr.Store.get_lower_bounds_exn store ~var
;;

let get_upper_bounds_exn { store; _ } ~var =
  Cstr.Store.get_upper_bounds_exn store ~var
;;

let fresh_tyvar { supply; store } =
  let var = Ty.Var.of_int supply in
  let store = Cstr.Store.add store ~var in
  let supply = supply + 1 in
  { store; supply }
;;
