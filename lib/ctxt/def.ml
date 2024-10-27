type t =
  { classish : Classish.t option
  ; fns : Fn.t list
  }

let empty = { classish = None; fns = [] }
let enter_classish t name = { t with classish = Some (Classish.create ~name ()) }
let enter_fn t ~name ~return = { t with fns = Fn.create ~name ~return () :: t.fns }

let exit_fn t =
  match t.fns with
  | _ :: fns -> { t with fns }
  | _ -> t
;;
