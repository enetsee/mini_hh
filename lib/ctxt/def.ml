type t =
  { classish : Classish.t option
  ; fns : Fn.t list
  }

let enter_classish name = { classish = Some (Classish.create ~name ()); fns = [] }
let enter_fn t ~name ~return = { t with fns = Fn.create ~name ~return () :: t.fns }

let exit_fn t =
  match t.fns with
  | _ :: fns -> { t with fns }
  | _ -> t
;;
