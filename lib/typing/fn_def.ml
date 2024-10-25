open Core
open Reporting

let synth
  (Lang.Fn_def.{ name; lambda = Lang.Lambda.{ lambda_sig; body }; where_constraints }, span)
  ~def_ctxt
  ~cont_ctxt
  =
  let Lang.Lambda_sig.{ ty_params; params; return } = Located.elem lambda_sig in
  (* Enter the function context so we have access to the return type when typing the body *)
  let def_ctxt = Ctxt.Def.enter_fn def_ctxt ~name ~return in
  (* Build the per-continuation context delta *)
  let delta =
    (* Bind each function parameter as a local variable *)
    let local =
      let Lang.Fn_param_defs.{ required; optional; variadic } = params in
      let f Located.{ elem = Lang.Fn_param_def.{ name; ty }; _ } = name, ty in
      let local = Ctxt.Local.(bind_all empty @@ List.map required ~f) in
      let local = Ctxt.Local.(bind_all local @@ List.map optional ~f:Fn.(compose f fst)) in
      Option.value_map variadic ~default:local ~f:(fun param ->
        let tm_var, ty = f param in
        Ctxt.Local.bind local tm_var ty)
    in
    (* Bind function-level type parameters *)
    let ty_param =
      let declared = Ctxt.Ty_param.(bind_all empty @@ List.map ~f:Lang.Ty_param_def.to_ty_param ty_params) in
      (* Treat all method level refinements as unconditional in the body *)
      let ty_param_where = Ctxt.Ty_param.(bind_all empty where_constraints) in
      let prov = Prov.def_where_clause span in
      Ctxt.Ty_param.meet declared ty_param_where ~prov
    in
    Ctxt.Cont.Delta.create ~ty_param ~local ()
  in
  let cont_ctxt = Ctxt.Cont.update cont_ctxt ~delta in
  (* Type the body *)
  let _body_delta = Expr_stmt.Seq.synth (body, span) ~def_ctxt ~cont_ctxt in
  ()
;;
