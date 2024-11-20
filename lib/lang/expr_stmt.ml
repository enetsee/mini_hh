open Core
open Reporting

(* ~~ Expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module rec Expr_node : sig
  type t =
    | Lit of Common.Lit.t
    | Local of Name.Tm_var.t
    | This
    | Is of Is.t
    | As of As.t
    | Binary of Binary.t
    | Unary of Unary.t
    | Lambda of Lambda.t
    | Ident of Name.Fn.t
    | Apply of Apply.t
    | Call of Call.t
  [@@deriving eq, compare, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    | Lit of Common.Lit.t
    | Local of Name.Tm_var.t
    | This
    | Is of Is.t
    | As of As.t
    | Binary of Binary.t
    | Unary of Unary.t
    | Lambda of Lambda.t
    | Ident of Name.Fn.t
    | Apply of Apply.t
    | Call of Call.t
  [@@deriving eq, compare, sexp, show]

  let elab_to_generic t ~bound_ty_params =
    match t with
    | Lit _ | Local _ | This | Ident _ -> t
    | Is is_ -> Is (Is.elab_to_generic is_ ~bound_ty_params)
    | As as_ -> As (As.elab_to_generic as_ ~bound_ty_params)
    | Binary binary -> Binary (Binary.elab_to_generic binary ~bound_ty_params)
    | Unary unary -> Unary (Unary.elab_to_generic unary ~bound_ty_params)
    | Lambda lambda -> Lambda (Lambda.elab_to_generic lambda ~bound_ty_params)
    | Apply call -> Apply (Apply.elab_to_generic call ~bound_ty_params)
    | Call call -> Call (Call.elab_to_generic call ~bound_ty_params)
  ;;
end

and Expr : sig
  type t = Expr_node.t Located.t [@@deriving eq, compare, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t = Expr_node.t Located.t [@@deriving eq, compare, sexp, show]

  let elab_to_generic t ~bound_ty_params =
    Located.map (Expr_node.elab_to_generic ~bound_ty_params) t
  ;;
end

(* ~~ Type application ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Apply : sig
  type t =
    { ctor : Expr.t
    ; ty_args : Ty.t list
    }
  [@@deriving compare, create, eq, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { ctor : Expr.t
    ; ty_args : Ty.t list
    }
  [@@deriving compare, create, eq, sexp, show]

  let elab_to_generic { ctor; ty_args } ~bound_ty_params =
    let ctor = Expr.elab_to_generic ctor ~bound_ty_params
    and ty_args = List.map ty_args ~f:(Ty.elab_to_generic ~bound_ty_params) in
    { ctor; ty_args }
  ;;
end

(* ~~ Calls ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Call : sig
  type t =
    { func : Expr.t
    ; args : Expr.t list
    ; unpacked_arg : Expr.t option
    }
  [@@deriving compare, create, eq, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { func : Expr.t
    ; args : Expr.t list
    ; unpacked_arg : Expr.t option
    }
  [@@deriving compare, create, eq, sexp, show]

  let elab_to_generic { func; args; unpacked_arg } ~bound_ty_params =
    let func = Expr.elab_to_generic func ~bound_ty_params
    and args = List.map args ~f:(Expr.elab_to_generic ~bound_ty_params)
    and unpacked_arg =
      Option.map unpacked_arg ~f:(Expr.elab_to_generic ~bound_ty_params)
    in
    { func; args; unpacked_arg }
  ;;
end

(* ~~ Lambdas ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Lambda : sig
  type t =
    { lambda_sig : Lambda_sig.t Located.t
    ; body : Seq.t
    }
  [@@deriving compare, create, eq, sexp, show]

  val empty : t
  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { lambda_sig : Lambda_sig.t Located.t
    ; body : Seq.t
    }
  [@@deriving compare, create, eq, sexp, show]

  let empty =
    { lambda_sig = Located.create_empty Lambda_sig.empty; body = Seq.empty }
  ;;

  let elab_to_generic { lambda_sig; body } ~bound_ty_params =
    let Lambda_sig.{ ty_params; params; return } = Located.elem lambda_sig in
    (* Bind function level generics *)
    let bound_ty_params =
      let declared_ty_params =
        Name.Ty_param.Set.of_list
        @@ List.map
             ~f:(fun Ty_param_def.{ name; _ } -> Located.elem name)
             ty_params
      in
      Set.union bound_ty_params declared_ty_params
    in
    let lambda_sig =
      let ty_params =
        List.map ~f:(Ty_param_def.elab_to_generic ~bound_ty_params) ty_params
      and params = Fn_param_defs.elab_to_generic params ~bound_ty_params
      and return = Ty.elab_to_generic return ~bound_ty_params in
      let elem = Lambda_sig.create ~ty_params ~params ~return () in
      Located.map (fun _ -> elem) lambda_sig
    in
    let body = Seq.elab_to_generic body ~bound_ty_params in
    create ~lambda_sig ~body ()
  ;;
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

  let empty =
    { ty_params = []
    ; params = Fn_param_defs.empty
    ; return = Ty.nothing Prov.empty
    }
  ;;
end

and Fn_param_defs : sig
  type t =
    { required : Fn_param_def.t Located.t list
    ; optional : (Fn_param_def.t Located.t * Expr.t) list
    ; variadic : Fn_param_def.t Located.t option
    }
  [@@deriving compare, create, eq, sexp, show]

  val empty : t
  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { required : Fn_param_def.t Located.t list
    ; optional : (Fn_param_def.t Located.t * Expr.t) list
    ; variadic : Fn_param_def.t Located.t option
    }
  [@@deriving compare, create, eq, sexp, show]

  let empty = { required = []; optional = []; variadic = None }

  let elab_to_generic { required; optional; variadic } ~bound_ty_params =
    let f fn_param_def =
      Located.map (Fn_param_def.elab_to_generic ~bound_ty_params) fn_param_def
    in
    let required = List.map ~f required
    and optional =
      List.map
        ~f:(fun (fn_param_def, expr) ->
          f fn_param_def, Expr.elab_to_generic expr ~bound_ty_params)
        optional
    and variadic = Option.map ~f variadic in
    { required; optional; variadic }
  ;;
end

(* ~~ Is refinements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Is : sig
  type t =
    { scrut : Expr.t
    ; ty_test : Ty.t
    }
  [@@deriving eq, compare, create, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { scrut : Expr.t
    ; ty_test : Ty.t
    }
  [@@deriving compare, create, eq, sexp, show]

  let elab_to_generic { scrut; ty_test } ~bound_ty_params =
    let scrut = Expr.elab_to_generic scrut ~bound_ty_params
    and ty_test = Ty.elab_to_generic ty_test ~bound_ty_params in
    { scrut; ty_test }
  ;;
end

(* ~~ As refinements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and As : sig
  type t =
    { scrut : Expr.t
    ; ty_assert : Ty.t
    }
  [@@deriving eq, compare, create, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { scrut : Expr.t
    ; ty_assert : Ty.t
    }
  [@@deriving eq, compare, create, sexp, show]

  let elab_to_generic { scrut; ty_assert } ~bound_ty_params =
    let scrut = Expr.elab_to_generic scrut ~bound_ty_params
    and ty_assert = Ty.elab_to_generic ty_assert ~bound_ty_params in
    { scrut; ty_assert }
  ;;
end

(* ~~ Binary expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Binary : sig
  type t =
    { binop : Binop.t
    ; lhs : Expr.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { binop : Binop.t
    ; lhs : Expr.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]

  let elab_to_generic { binop; lhs; rhs } ~bound_ty_params =
    let lhs = Expr.elab_to_generic lhs ~bound_ty_params
    and rhs = Expr.elab_to_generic rhs ~bound_ty_params in
    { binop; lhs; rhs }
  ;;
end

(* ~~ Unary expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Unary : sig
  type t =
    { unop : Unop.t
    ; operand : Expr.t
    }
  [@@deriving eq, compare, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { unop : Unop.t
    ; operand : Expr.t
    }
  [@@deriving eq, compare, sexp, show]

  let elab_to_generic { unop; operand } ~bound_ty_params =
    let operand = Expr.elab_to_generic operand ~bound_ty_params in
    { unop; operand }
  ;;
end

(* ~~ Statements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Stmt_node : sig
  type t =
    | Expr of Expr.t
    | Assign of Assign.t
    | If of If.t
    | Seq of Seq.t
    | Return of Expr.t option
    | Unpack of Unpack.t
  [@@deriving eq, compare, sexp, show, variants]

  val noop : t
  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    | Expr of Expr.t
    | Assign of Assign.t
    | If of If.t
    | Seq of Seq.t
    | Return of Expr.t option
    | Unpack of Unpack.t
  [@@deriving eq, compare, sexp, show, variants]

  let noop = Seq (Seq [])

  let elab_to_generic t ~bound_ty_params =
    match t with
    | Expr expr -> Expr (Expr.elab_to_generic expr ~bound_ty_params)
    | Assign assign -> Assign (Assign.elab_to_generic assign ~bound_ty_params)
    | If if_ -> If (If.elab_to_generic if_ ~bound_ty_params)
    | Seq seq -> Seq (Seq.elab_to_generic seq ~bound_ty_params)
    | Return expr_opt ->
      Return (Option.map expr_opt ~f:(Expr.elab_to_generic ~bound_ty_params))
    | Unpack unpack -> Unpack (Unpack.elab_to_generic unpack ~bound_ty_params)
  ;;
end

and Stmt : sig
  type t = Stmt_node.t Located.t [@@deriving eq, compare, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t = Stmt_node.t Located.t [@@deriving eq, compare, sexp, show]

  let elab_to_generic t ~bound_ty_params =
    Located.map (Stmt_node.elab_to_generic ~bound_ty_params) t
  ;;
end

(* ~~ Assignment ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Assign : sig
  type t =
    { lvalue : Lvalue.t Located.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { lvalue : Lvalue.t Located.t
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]

  let elab_to_generic { lvalue; rhs } ~bound_ty_params =
    let rhs = Expr.elab_to_generic rhs ~bound_ty_params in
    { lvalue; rhs }
  ;;
end

(* ~~ If ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and If : sig
  type t =
    { cond : Expr.t
    ; then_ : Stmt.t
    ; else_ : Stmt.t
    }
  [@@deriving eq, compare, create, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { cond : Expr.t
    ; then_ : Stmt.t
    ; else_ : Stmt.t
    }
  [@@deriving eq, compare, create, sexp, show]

  let elab_to_generic { cond; then_; else_ } ~bound_ty_params =
    let cond = Expr.elab_to_generic cond ~bound_ty_params
    and then_ = Stmt.elab_to_generic then_ ~bound_ty_params
    and else_ = Stmt.elab_to_generic else_ ~bound_ty_params in
    { cond; then_; else_ }
  ;;
end

(* ~~ Sequence ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Seq : sig
  type t = Seq of Stmt.t list
  [@@ocaml.unboxed] [@@deriving eq, compare, sexp, show]

  val empty : t
  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t = Seq of Stmt.t list
  [@@ocaml.unboxed] [@@deriving eq, compare, sexp, show]

  let empty = Seq []

  let elab_to_generic (Seq stmts) ~bound_ty_params =
    Seq (List.map stmts ~f:(Stmt.elab_to_generic ~bound_ty_params))
  ;;
end

(* ~~ Unpack ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Unpack : sig
  type t =
    { tm_var : Name.Tm_var.t Located.t
    ; ty_params : Name.Ty_param.t Located.t list
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  type t =
    { tm_var : Name.Tm_var.t Located.t
    ; ty_params : Name.Ty_param.t Located.t list
    ; rhs : Expr.t
    }
  [@@deriving eq, compare, create, sexp, show]

  let elab_to_generic t ~bound_ty_params =
    let rhs = Expr.elab_to_generic t.rhs ~bound_ty_params in
    { t with rhs }
  ;;
end

(* ~~ L-values ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Lvalue : sig
  type t = Local of Name.Tm_var.t
  [@@deriving eq, compare, sexp, show, variants]
end = struct
  type t = Local of Name.Tm_var.t
  [@@deriving eq, compare, sexp, show, variants]
end
