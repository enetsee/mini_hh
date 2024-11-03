open Core
open Common
open Reporting

type _ Effect.t +=
  | Gen_fresh_ty_params : int -> Name.Ty_param.t list Effect.t (** Get n globally fresh type parameter names *)
  | Ask_up :
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      }
      -> Ty.t list option Effect.t
      (** Get the instantation of the constructor type [of_] at a superclass given by the constructor [at]. This will be
          [None] if [of_] does not extend or implement [at] *)
  | Ask_ty_param_variances : Name.Ctor.t -> Variance.t Located.t list option Effect.t
      (** Get the declared variances for the type parameters of a constructor name. The will be [None] is the
          constructor is not bound*)
  | Log_enter_refinement :
      { ty_test : Ty.t
      ; ty_scrut : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Ty.t * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_exit_refinement :
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      }
      -> (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option) Effect.t
  | Log_enter_refine_ty :
      { ty_test : Ty.t
      ; ty_scrut : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Ty.t * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_exit_refine_ty :
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      }
      -> (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option) Effect.t
  | Log_enter_refine_existential_scrut :
      { prov_scrut : Prov.t
      ; ty_exists : Ty.Exists.t
      ; ty_test : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Prov.t * Ty.Exists.t * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_exit_refine_existential_scrut :
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      }
      -> (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option) Effect.t
  | Log_enter_refine_existential_test :
      { ty_scrut : Ty.t
      ; prov_test : Prov.t
      ; ty_exists : Ty.Exists.t
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Ty.t * Prov.t * Ty.Exists.t * Ctxt.Cont.t) Effect.t
  | Log_exit_refine_existential_test :
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      }
      -> (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option) Effect.t
  | Log_enter_refine_union_scrut :
      { prov_scrut : Prov.t
      ; tys_scrut : Ty.t list
      ; ty_test : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Prov.t * Ty.t list * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_exit_refine_union_scrut :
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      }
      -> (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option) Effect.t
  | Log_enter_refine_union_test :
      { ty_scrut : Ty.t
      ; prov_test : Prov.t
      ; tys_test : Ty.t list
      ; ctxt_cont : Ctxt.Cont.t
      }
      -> (Ty.t * Prov.t * Ty.t list * Ctxt.Cont.t) Effect.t
  | Log_exit_refine_union_test :
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      }
      -> (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option) Effect.t

let gen_fresh_ty_params n = Effect.perform (Gen_fresh_ty_params n)
let ask_up ~of_ ~at = Effect.perform (Ask_up { of_; at })
let ask_ty_param_variances ctor = Effect.perform (Ask_ty_param_variances ctor)

let log_enter_refinement ~ty_test ~ty_scrut ~ctxt_cont =
  Effect.perform (Log_enter_refinement { ty_test; ty_scrut; ctxt_cont })
;;

let log_exit_refinement (ty_rfmt, ty_param_rfmt_opt) =
  Effect.perform (Log_exit_refinement { ty_rfmt; ty_param_rfmt_opt })
;;

let log_enter_refine_ty ~ty_test ~ty_scrut ~ctxt_cont =
  Effect.perform (Log_enter_refine_ty { ty_test; ty_scrut; ctxt_cont })
;;

let log_exit_refine_ty (ty_rfmt, ty_param_rfmt_opt) = Effect.perform (Log_exit_refine_ty { ty_rfmt; ty_param_rfmt_opt })

let log_enter_refine_existential_scrut prov_scrut ty_exists ty_test ctxt_cont =
  Effect.perform (Log_enter_refine_existential_scrut { prov_scrut; ty_exists; ty_test; ctxt_cont })
;;

let log_exit_refine_existential_scrut (ty_rfmt, ty_param_rfmt_opt) =
  Effect.perform (Log_exit_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt })
;;

let log_enter_refine_existential_test ty_scrut prov_test ty_exists ctxt_cont =
  Effect.perform (Log_enter_refine_existential_test { ty_scrut; prov_test; ty_exists; ctxt_cont })
;;

let log_exit_refine_existential_test (ty_rfmt, ty_param_rfmt_opt) =
  Effect.perform (Log_exit_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt })
;;

let run comp src oracle =
  let src_ref = ref src in
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          (* ~~ Enter / exit top-level ~~ *)
          | Log_enter_refinement { ty_test; ty_scrut; ctxt_cont } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont))
          | Log_exit_refinement { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt))
          (* ~~ Enter / exit type ~~ *)
          | Log_enter_refine_ty { ty_test; ty_scrut; ctxt_cont } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont))
          | Log_exit_refine_ty { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt))
          (* ~~ Enter / exit existential scrutinee ~~ *)
          | Log_enter_refine_existential_scrut { prov_scrut; ty_exists; ty_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (prov_scrut, ty_exists, ty_test, ctxt_cont))
          | Log_exit_refine_existential_scrut { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt))
          (* ~~ Enter / exit existential test ~~ *)
          | Log_enter_refine_existential_test { ty_scrut; prov_test; ty_exists; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty_scrut, prov_test, ty_exists, ctxt_cont))
          | Log_exit_refine_existential_test { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt))
          (* ~~ Enter / exit union scrut ~~ *)
          | Log_enter_refine_union_scrut { prov_scrut; tys_scrut; ty_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (prov_scrut, tys_scrut, ty_test, ctxt_cont))
          | Log_exit_refine_union_scrut { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt))
          (* ~~ Enter / exit union test ~~ *)
          | Log_enter_refine_union_test { ty_scrut; prov_test; tys_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty_scrut, prov_test, tys_test, ctxt_cont))
          | Log_exit_refine_union_test { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt))
          (* ~~ Enter / exit intersection scrut ~~ *)
          (* ~~ Enter / exit intersection test ~~ *)
          (* ~~ Enter / exit constructor ~~ *)
          (* ~~ Enter / exit constructor type argument ~~ *)
          | Gen_fresh_ty_params n ->
            let offset = !src_ref in
            src_ref := offset + n;
            let names = List.init n ~f:(fun i -> Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset)) in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k names)
          | Ask_up { of_; at } ->
            let ty_args_opt = Oracle.up oracle ~of_ ~at in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ty_args_opt)
          | Ask_ty_param_variances ctor ->
            let ty_param_vars_opt = Oracle.param_variances_opt oracle ~ctor in
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Effect.Deep.continue k ty_param_vars_opt)
          | _ -> None)
    ; retc = (fun res -> res, !src_ref)
    ; exnc = (fun exn -> raise exn)
    }
;;

(* type status =
  | Complete of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      }
  | Failed of Exn.t
  | Entered_refinement of
      { ty_test : Ty.t
      ; ty_scrut : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ty.t * Ty.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_refinement of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, status) Effect.Deep.continuation
      }
  | Entered_refine_ty of
      { ty_test : Ty.t
      ; ty_scrut : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ty.t * Ty.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_refine_ty of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, status) Effect.Deep.continuation
      }
  | Entered_refine_existential_scrut of
      { prov_scrut : Prov.t
      ; ty_exists : Ty.Exists.t
      ; ty_test : Ty.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Prov.t * Ty.Exists.t * Ty.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_refine_existential_scrut of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, status) Effect.Deep.continuation
      }
  | Entered_refine_existential_test of
      { ty_scrut : Ty.t
      ; prov_test : Prov.t
      ; ty_exists : Ty.Exists.t
      ; ctxt_cont : Ctxt.Cont.t
      ; k : (Ty.t * Prov.t * Ty.Exists.t * Ctxt.Cont.t, status) Effect.Deep.continuation
      }
  | Exited_refine_existential_test of
      { ty_rfmt : Ty.Refinement.t
      ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
      ; k : (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option, status) Effect.Deep.continuation
      }
  | Asked_up of
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      ; k : (Ty.t list option, status) Effect.Deep.continuation
      }
  | Asked_ty_param_variances of
      { ctor : Name.Ctor.t
      ; k : (Variance.t Located.t list option, status) Effect.Deep.continuation
      }
  | Requested_fresh_ty_params of
      { n : int
      ; k : (Name.Ty_param.t list, status) Effect.Deep.continuation
      } *)

(* let next status ~oracle ~ty_param_name_source =
  match status with
  | Entered_refinement { ty_test; ty_scrut; ctxt_cont; k } ->
    Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont), ty_param_name_source
  | Exited_refinement { ty_rfmt; ty_param_rfmt_opt; k } ->
    Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt), ty_param_name_source
  | Entered_refine_ty { ty_test; ty_scrut; ctxt_cont; k } ->
    Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont), ty_param_name_source
  | Exited_refine_ty { ty_rfmt; ty_param_rfmt_opt; k } ->
    Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt), ty_param_name_source


  | Entered_refine_existential_scrut { prov_scrut;ty_exists; ty_test; ctxt_cont; k } ->
    Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont), ty_param_name_source
  | Exited_refine_ty { ty_rfmt; ty_param_rfmt_opt; k } ->
    Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt), ty_param_name_source

  | Asked_up { of_; at; k } ->
    let ty_args_opt = Oracle.up oracle ~of_ ~at in
    Effect.Deep.continue k ty_args_opt, ty_param_name_source
  | Asked_ty_param_variances { ctor; k } ->
    let ty_param_vars_opt = Oracle.param_variances_opt oracle ~ctor in
    Effect.Deep.continue k ty_param_vars_opt, ty_param_name_source
  | Requested_fresh_ty_params { n; k } ->
    let offset = ty_param_name_source in
    let ty_param_name_source = offset + n in
    let names = List.init n ~f:(fun i -> Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset)) in
    Effect.Deep.continue k names, ty_param_name_source
  | Complete _ | Failed _ -> status, ty_param_name_source
;;

let debug comp =
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Log_enter_refinement { ty_test; ty_scrut; ctxt_cont } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Entered_refinement { ty_test; ty_scrut; ctxt_cont; k })
          | Log_exit_refinement { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Exited_refinement { ty_rfmt; ty_param_rfmt_opt; k })
          | Log_enter_refine_ty { ty_test; ty_scrut; ctxt_cont } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Entered_refine_ty { ty_test; ty_scrut; ctxt_cont; k })
          | Log_exit_refine_ty { ty_rfmt; ty_param_rfmt_opt } ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Exited_refine_ty { ty_rfmt; ty_param_rfmt_opt; k })
          | Gen_fresh_ty_params n ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Requested_fresh_ty_params { n; k })
          | Ask_up { of_; at } -> Some (fun (k : (a, _) Effect.Deep.continuation) -> Asked_up { of_; at; k })
          | Ask_ty_param_variances ctor ->
            Some (fun (k : (a, _) Effect.Deep.continuation) -> Asked_ty_param_variances { ctor; k })
          | _ -> None)
    ; retc = (fun (ty_rfmt, ty_param_rfmt_opt) -> Complete { ty_rfmt; ty_param_rfmt_opt })
    ; exnc = (fun exn -> Failed exn)
    }
;; *)
