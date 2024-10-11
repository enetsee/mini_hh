open Core

type t =
  | Empty
  | Witness of Witness.t
  | Witnesses of Witness.t list
  | Refines of
      { prov_scrut : t
      ; prov_test : t
      }
[@@deriving compare, eq, sexp, show, variants, yojson]

(* Lifted witnesses *)
let witness span = Witness (Witness.witness span)
let witnesses spans = Witnesses (List.map ~f:(fun span -> Witness.witness span) spans)
let lit_null span = Witness (Witness.lit_null span)
let lit_bool span = Witness (Witness.lit_bool span)
let lit_lnum span = Witness (Witness.lit_lnum span)
let lit_dnum span = Witness (Witness.lit_dnum span)
let lit_const_string span = Witness (Witness.lit_bool span)
