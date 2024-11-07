open Reporting

module Minimal = struct
  type t = { name : Name.Ctor.t Located.t } [@@deriving create]

  let pp ppf t = Fmt.(vbox @@ record ~sep:cut [ field "name" (fun { name } -> name) @@ Located.pp Name.Ctor.pp ]) ppf t
end

include Minimal
include Pretty.Make (Minimal)
