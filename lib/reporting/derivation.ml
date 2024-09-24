type t = Deriv of t [@@deriving compare, eq, sexp, show, variants, yojson]
