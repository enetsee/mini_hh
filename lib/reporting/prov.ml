type t =
  | Empty
  | Witness of Witness.t
  | Refines of
      { prov_scrut : t
      ; prov_test : t
      }
[@@deriving compare, eq, sexp, show, variants, yojson]

let witness loc = Witness (Witness.witness loc)
