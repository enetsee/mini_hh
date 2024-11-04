open Reporting

module Minimal = struct
  (** A function context gives us
      - the function name (not sure we need it)
      - the return type
      - type parameter and this refinements apply to any enclosing class, interface
        or trait*)
  type t =
    { name : Name.Fn.t Located.t
    ; return : Ty.t
    }
  [@@deriving create]

  let pp ppf t =
    Fmt.(
      vbox
      @@ record
           ~sep:cut
           [ field "name" (fun { name; _ } -> name) @@ Located.pp Name.Fn.pp
           ; field "return type" (fun { return; _ } -> return) @@ Ty.pp
           ])
      ppf
      t
  ;;
end

include Minimal
include Pretty.Make (Minimal)

let return { return; _ } = return
