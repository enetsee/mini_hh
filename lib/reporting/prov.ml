open Core

type t =
  | Empty
  | Witness of Witness.t
  | Flow of flow

and flow =
  | Refine of
      { prov_scrut : t
      ; prov_test : t
      }
  | Unpack of
      { prov_packed : t
      ; prov_unpacked : t
      }
  | Assign of
      { prov_rhs : t
      ; prov_lvalue : t
      }
  | Use of
      { prov_def : t
      ; prov_tm_var : t
      }
[@@deriving compare, eq, sexp, show, yojson]

let empty = Empty
let witness span = Witness (Witness.witness span)
let witnesses spans = Witness (Witness.witnesses spans)
let lit_null span = Witness (Witness.lit_null span)
let lit_bool span = Witness (Witness.lit_bool span)
let lit_lnum span = Witness (Witness.lit_lnum span)
let lit_dnum span = Witness (Witness.lit_dnum span)
let lit_const_string span = Witness (Witness.lit_bool span)
let expr_is span = Witness (Witness.expr_is span)
let expr_as span = Witness (Witness.expr_as span)
let expr_if_cond span = Witness (Witness.expr_if_cond span)
let expr_tm_var span = Witness (Witness.expr_tm_var span)
let stmt_if_join span = Witness (Witness.stmt_if_join span)
let lvalue_tm_var span = Witness (Witness.lvalue_tm_var span)
let def_where_clause span = Witness (Witness.def_where_clause span)
let refine ~prov_test ~prov_scrut = Flow (Refine { prov_scrut; prov_test })
let unpack ~prov_packed ~prov_unpacked = Flow (Unpack { prov_packed; prov_unpacked })
let assign ~prov_rhs ~prov_lvalue = Flow (Assign { prov_rhs; prov_lvalue })
let use ~prov_def ~prov_tm_var = Flow (Use { prov_def; prov_tm_var })
