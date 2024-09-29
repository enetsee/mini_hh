open Core
open Reporting

(* ~~ Expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module rec Expr_node : sig
  type t =
    | Lit of Lit.t
    | Local of Name.Tm_var.t Located.t
    | Is of Is.t
    | As of As.t
    | Binary of Binary.t
    | Unary of Unary.t
    | Lambda of Lambda.t
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    | Lit of Lit.t
    | Local of Name.Tm_var.t Located.t
    | Is of Is.t
    | As of As.t
    | Binary of Binary.t
    | Unary of Unary.t
    | Lambda of Lambda.t
  [@@deriving eq, compare, sexp, show]
end

and Expr : sig
  type t = Expr_node.t Located.t [@@deriving eq, compare, sexp, show]
end = struct
  type t = Expr_node.t Located.t [@@deriving eq, compare, sexp, show]
end

(* ~~ Lambdas ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Lambda : sig
  type t =
    { signature : Lambda_sig.t Located.t
    ; body : Seq.t Located.t
    }
  [@@deriving compare, create, eq, sexp, show]
end = struct
  type t =
    { signature : Lambda_sig.t Located.t
    ; body : Seq.t Located.t
    }
  [@@deriving compare, create, eq, sexp, show]
end

and Lambda_sig : sig
  type t =
    { params : Fn_params_def.t Located.t
    ; return : Ty.t
    }
  [@@deriving compare, create, eq, sexp, show]
end = struct
  type t =
    { params : Fn_params_def.t Located.t
    ; return : Ty.t
    }
  [@@deriving compare, create, eq, sexp, show]
end

and Fn_params_def : sig
  type t =
    { required : Fn_param_def.t Located.t list
    ; optional : (Fn_param_def.t Located.t * Expr.t) Located.t list
    ; variadic : Fn_param_def.t Located.t option
    }
  [@@deriving compare, create, eq, sexp, show]
end = struct
  type t =
    { required : Fn_param_def.t Located.t list
    ; optional : (Fn_param_def.t Located.t * Expr.t) Located.t list
    ; variadic : Fn_param_def.t Located.t option
    }
  [@@deriving compare, create, eq, sexp, show]
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
  [@@deriving compare, create, eq, sexp, show]
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
  type t = Stmt_node.t Located.t [@@deriving eq, compare, sexp, show]
end = struct
  type t = Stmt_node.t Located.t [@@deriving eq, compare, sexp, show]
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
