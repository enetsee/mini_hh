open Expr_stmt

(* ~~ Expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

module Lit = Lit
module Expr = Expr
module Expr_node = Expr_node
module Is = Is
module Binary = Binary
module Binop = Binop
module Unary = Unary
module Unop = Unop
include Expr

(* ~~ Statements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

module Stmt = Stmt
module Stmt_node = Stmt_node
module Assign = Assign
module If = If
module Seq = Seq
include Stmt

(* ~~ Lvalues ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

module Lvalue = Lvalue

(* ~~ Definitions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* module Fn_def = Fn_def
   module Fn_param = Fn_param *)
