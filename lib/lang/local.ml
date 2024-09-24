open Core

module Minimal = struct
  (* TODO(mjt) add idents for fast comparison *)
  type t = Local of Name.Tm_var.t [@@deriving eq, compare, sexp, show] [@@ocaml.unboxed]
end

include Minimal

module Map = struct
  include Map.Make (Minimal)

  let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf @@ Map.to_alist t
end
