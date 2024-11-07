module Minimal = struct
  type t =
    { classish : Classish_def.t option
    ; fns : Fn_def.t list
    }

  let pp ppf t =
    Fmt.(
      vbox
      @@ record
           ~sep:cut
           [ field "classish definition" (fun { classish; _ } -> classish)
             @@ option ~none:(any "(none)") Classish_def.pp
           ; field "function definitions" (fun { fns; _ } -> fns) @@ list ~sep:cut Fn_def.pp
           ])
      ppf
      t
  ;;
end

include Minimal
include Pretty.Make (Minimal)

let empty = { classish = None; fns = [] }
let enter_classish t name = { t with classish = Some (Classish_def.create ~name ()) }
let enter_fn t ~name ~return = { t with fns = Fn_def.create ~name ~return () :: t.fns }

let exit_fn t =
  match t.fns with
  | _ :: fns -> { t with fns }
  | _ -> t
;;

let ask_return_ty { fns; _ } =
  match fns with
  | fn :: _ -> Some (Fn_def.return fn)
  | _ -> None
;;
