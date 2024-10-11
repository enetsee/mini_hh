open Core
open Reporting

(* ~~ Expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module rec Expr_node : sig
  type t =
    | Lit of Lit.t
    | Local of Name.Tm_var.t
    | This
    | Is of Is.t
    | As of As.t
    | Binary of Binary.t
    | Unary of Unary.t
    | Lambda of Lambda.t
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    | Lit of Lit.t
    | Local of Name.Tm_var.t
    | This
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
    { lambda_sig : Lambda_sig.t Located.t
    ; body : Seq.t
    }
  [@@deriving compare, create, eq, sexp, show]

  val empty : t
end = struct
  type t =
    { lambda_sig : Lambda_sig.t Located.t
    ; body : Seq.t
    }
  [@@deriving compare, create, eq, sexp, show]

  let empty = { lambda_sig = Located.create_empty Lambda_sig.empty; body = Seq.empty }
end

and Lambda_sig : sig
  type t =
    { ty_params : Ty_param_def.t list
    ; params : Fn_param_defs.t
    ; return : Ty.t
    }
  [@@deriving compare, create, eq, sexp, show]

  val empty : t
end = struct
  type t =
    { ty_params : Ty_param_def.t list
    ; params : Fn_param_defs.t
    ; return : Ty.t
    }
  [@@deriving compare, create, eq, sexp, show]

  let empty = { ty_params = []; params = Fn_param_defs.empty; return = Ty.nothing Prov.empty }
end

and Fn_param_defs : sig
  type t =
    { required : Fn_param_def.t Located.t list
    ; optional : (Fn_param_def.t Located.t * Expr.t) list
    ; variadic : Fn_param_def.t Located.t option
    }
  [@@deriving compare, create, eq, sexp, show]

  val empty : t
end = struct
  type t =
    { required : Fn_param_def.t Located.t list
    ; optional : (Fn_param_def.t Located.t * Expr.t) list
    ; variadic : Fn_param_def.t Located.t option
    }
  [@@deriving compare, create, eq, sexp, show]

  let empty = { required = []; optional = []; variadic = None }
end

(* ~~ Is refinements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Is : sig
  type t =
    { scrut : Expr.t
    ; ty_test : Ty.t
    }
  [@@deriving eq, compare, create, sexp, show]
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
  [@@deriving eq, compare, create, sexp, show]
end = struct
  type t =
    { binop : Binop.t
    ; lhs : Expr.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]
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
    | Noop
  [@@deriving eq, compare, sexp, show, variants]
end = struct
  type t =
    | Expr of Expr.t
    | Return of Expr.t option
    | Assign of Assign.t
    | If of If.t
    | Seq of Seq.t
    | Noop
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
    { lvalue : Lvalue.t Located.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]
end = struct
  type t =
    { lvalue : Lvalue.t Located.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]
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

  val empty : t
end = struct
  type t = Seq of Stmt.t list [@@ocaml.unboxed] [@@deriving eq, compare, sexp, show]

  let empty = Seq []
end

(* ~~ L-values ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Lvalue : sig
  type t = Local of Name.Tm_var.t [@@deriving eq, compare, sexp, show, variants]
end = struct
  type t = Local of Name.Tm_var.t [@@deriving eq, compare, sexp, show, variants]
end
