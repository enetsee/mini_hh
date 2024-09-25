open Core
open Reporting

(* ~~ Expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module rec Expr_node : sig
  type t =
    | Lit of Lit.t
    | Local of Name.Tm_var.t
    | Is of Is.t
    | As of As.t
    | Binary of Binary.t
    | Unary of Unary.t
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    | Lit of Lit.t
    | Local of Name.Tm_var.t
    | Is of Is.t
    | As of As.t
    | Binary of Binary.t
    | Unary of Unary.t
  [@@deriving eq, compare, sexp, show]
end

and Expr : sig
  type t =
    { node : Expr_node.t
    ; loc : Loc.t
    }
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    { node : Expr_node.t
    ; loc : Loc.t
    }
  [@@deriving eq, compare, sexp, show]
end

(* ~~ Is refinements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Is : sig
  type t =
    { scrut : Expr.t
    ; ty_test : Ty.t
    }
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    { scrut : Expr.t
    ; ty_test : Ty.t
    }
  [@@deriving eq, compare, sexp, show]
end

(* ~~ As refinements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and As : sig
  type t =
    { scrut : Expr.t
    ; ty_assert : Ty.t
    }
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    { scrut : Expr.t
    ; ty_assert : Ty.t
    }
  [@@deriving eq, compare, sexp, show]
end

(* ~~ Binary expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Binary : sig
  type t =
    { binop : Binop.t
    ; lhs : Expr.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    { binop : Binop.t
    ; lhs : Expr.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, sexp, show]
end

(* ~~ Unary expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Unary : sig
  type t =
    { unop : Unop.t
    ; operand : Expr.t
    }
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    { unop : Unop.t
    ; operand : Expr.t
    }
  [@@deriving eq, compare, sexp, show]
end

(* ~~ Statements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Stmt_node : sig
  type t =
    | Expr of Expr.t
    | Return of Expr.t option
    | Assign of Assign.t
    | If of If.t
    | Seq of Seq.t
  [@@deriving eq, compare, sexp, show, variants]
end = struct
  type t =
    | Expr of Expr.t
    | Return of Expr.t option
    | Assign of Assign.t
    | If of If.t
    | Seq of Seq.t
  [@@deriving eq, compare, sexp, show, variants]
end

and Stmt : sig
  type t =
    { node : Stmt_node.t
    ; loc : Loc.t
    }
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    { node : Stmt_node.t
    ; loc : Loc.t
    }
  [@@deriving eq, compare, sexp, show]
end

(* ~~ Assigment ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Assign : sig
  type t =
    { lvalue : Lvalue.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    { lvalue : Lvalue.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, sexp, show]
end

(* ~~ If ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and If : sig
  type t =
    { cond : Expr.t
    ; then_ : Stmt.t
    ; else_ : Stmt.t
    }
  [@@deriving eq, compare, create, sexp, show]
end = struct
  type t =
    { cond : Expr.t
    ; then_ : Stmt.t
    ; else_ : Stmt.t
    }
  [@@deriving eq, compare, create, sexp, show]
end

(* ~~ Sequence ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Seq : sig
  type t = Seq of Stmt.t list [@@ocaml.unboxed] [@@deriving eq, compare, sexp, show]
end = struct
  type t = Seq of Stmt.t list [@@ocaml.unboxed] [@@deriving eq, compare, sexp, show]
end

(* ~~ L-values ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Lvalue : sig
  type t = Local of Name.Tm_var.t [@@deriving eq, compare, sexp, show, variants]
end = struct
  type t = Local of Name.Tm_var.t [@@deriving eq, compare, sexp, show, variants]
end
