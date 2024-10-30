module Minimal = struct
  type t =
    { classish : Classish.t option
    ; fns : Fn.t list
    }

  let pp ppf t =
    Fmt.(
      vbox
      @@ record
           ~sep:cut
           [ field "classish definition" (fun { classish; _ } -> classish) @@ option ~none:(any "(none)") Classish.pp
           ; field "function definitions" (fun { fns; _ } -> fns) @@ list ~sep:cut Fn.pp
           ])
      ppf
      t
  ;;
end

include Minimal
include Pretty.Make (Minimal)

let empty = { classish = None; fns = [] }
let enter_classish t name = { t with classish = Some (Classish.create ~name ()) }
let enter_fn t ~name ~return = { t with fns = Fn.create ~name ~return () :: t.fns }

let exit_fn t =
  match t.fns with
  | _ :: fns -> { t with fns }
  | _ -> t
;;
