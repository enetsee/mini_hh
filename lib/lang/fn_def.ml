open Core
open Reporting

type t =
  { name : Name.Fn.t Located.t
  ; lambda : Expr_stmt.Lambda.t
  ; where_constraints : Ty.Param.t list
  }
[@@deriving compare, create, eq, sexp, show]

let elab_to_generic { name; lambda; where_constraints } ~bound_ty_params =
  (* This is a bit awkward - we need to bind the type parameters in the
     lambda before we elaborate the where constraints.. *)
  let Expr_stmt.Lambda.{ lambda_sig; body } = lambda in
  let Expr_stmt.Lambda_sig.{ ty_params; params; return } =
    Located.elem lambda_sig
  in
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
  let lambda =
    let lambda_sig =
      let ty_params =
        List.map ~f:(Ty_param_def.elab_to_generic ~bound_ty_params) ty_params
      and params =
        Expr_stmt.Fn_param_defs.elab_to_generic params ~bound_ty_params
      and return = Ty.elab_to_generic return ~bound_ty_params in
      let elem = Expr_stmt.Lambda_sig.create ~ty_params ~params ~return () in
      Located.map (fun _ -> elem) lambda_sig
    in
    let body = Expr_stmt.Seq.elab_to_generic body ~bound_ty_params in
    Expr_stmt.Lambda.create ~lambda_sig ~body ()
  in
  let where_constraints =
    List.map ~f:(Ty.Param.elab_to_generic ~bound_ty_params) where_constraints
  in
  { name; lambda; where_constraints }
;;
