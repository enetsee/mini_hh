open Core
open Common
open Reporting

type side =
  | Scrut
  | Test

let show_side = function
  | Scrut -> "scrut"
  | Test -> "test"
;;

type elem =
  | Refinement
  | Ty
  | Exists of side
  | Union of side
  | Inter of side
  | Top_level_generic of side
  | Ctor
  | Ctor_arg

let show_elem = function
  | Refinement -> "refinement"
  | Ty -> "ty"
  | Exists side -> Format.sprintf "exists (%s)" @@ show_side side
  | Union side -> Format.sprintf "union (%s)" @@ show_side side
  | Inter side -> Format.sprintf "inter (%s)" @@ show_side side
  | Top_level_generic side ->
    Format.sprintf "top-level generic (%s)" @@ show_side side
  | Ctor -> "ctor"
  | Ctor_arg -> "ctor arg"
;;

type exit =
  { elem : elem
  ; ty_rfmt : Ty.Refinement.t
  ; ty_param_rfmt_opt : (Prov.t * Ctxt.Ty_param.Refinement.t) option
  }

type enter_ty =
  { ty_test : Ty.t
  ; ty_scrut : Ty.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_existential_scrut =
  { prov_scrut : Prov.t
  ; ty_exists : Ty.Exists.t
  ; ty_test : Ty.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_existential_test =
  { ty_scrut : Ty.t
  ; prov_test : Prov.t
  ; ty_exists : Ty.Exists.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_union_scrut =
  { prov_scrut : Prov.t
  ; tys_scrut : Ty.t list
  ; ty_test : Ty.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_union_test =
  { ty_scrut : Ty.t
  ; prov_test : Prov.t
  ; tys_test : Ty.t list
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_inter_scrut =
  { prov_scrut : Prov.t
  ; tys_scrut : Ty.t list
  ; ty_test : Ty.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_inter_test =
  { ty_scrut : Ty.t
  ; prov_test : Prov.t
  ; tys_test : Ty.t list
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_top_level_generic_scrut =
  { prov_scrut : Prov.t
  ; name_scrut : Name.Ty_param.t
  ; ty_test : Ty.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_top_level_generic_test =
  { ty_scrut : Ty.t
  ; prov_test : Prov.t
  ; name_test : Name.Ty_param.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_ctor =
  { prov_scrut : Prov.t
  ; ctor_scrut : Ty.Ctor.t
  ; prov_test : Prov.t
  ; ctor_test : Ty.Ctor.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type enter_ctor_arg =
  { ty_scrut : Ty.t
  ; ty_test : Ty.t
  ; variance : Variance.t Located.t
  ; ctxt_cont : Ctxt.Cont.t
  }

type ask_up =
  { of_ : Ty.Ctor.t
  ; at : Name.Ctor.t
  }

type _ Effect.t +=
  | Request_fresh_ty_params : int -> Name.Ty_param.t list Effect.t
  | Ask_up : ask_up -> Oracle.Classish.instantiation Effect.t
  | Ask_ty_param_variances :
      Name.Ctor.t
      -> Variance.t Located.t list option Effect.t
  | Log_exit :
      exit
      -> (Ty.Refinement.t * (Prov.t * Ctxt.Ty_param.Refinement.t) option)
           Effect.t
  | Log_enter_refinement : enter_ty -> (Ty.t * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_enter_ty : enter_ty -> (Ty.t * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_enter_existential_scrut :
      enter_existential_scrut
      -> (Prov.t * Ty.Exists.t * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_enter_existential_test :
      enter_existential_test
      -> (Ty.t * Prov.t * Ty.Exists.t * Ctxt.Cont.t) Effect.t
  | Log_enter_union_scrut :
      enter_union_scrut
      -> (Prov.t * Ty.t list * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_enter_union_test :
      enter_union_test
      -> (Ty.t * Prov.t * Ty.t list * Ctxt.Cont.t) Effect.t
  | Log_enter_inter_scrut :
      enter_inter_scrut
      -> (Prov.t * Ty.t list * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_enter_inter_test :
      enter_inter_test
      -> (Ty.t * Prov.t * Ty.t list * Ctxt.Cont.t) Effect.t
  | Log_enter_top_level_generic_scrut :
      enter_top_level_generic_scrut
      -> (Prov.t * Name.Ty_param.t * Ty.t * Ctxt.Cont.t) Effect.t
  | Log_enter_top_level_generic_test :
      enter_top_level_generic_test
      -> (Ty.t * Prov.t * Name.Ty_param.t * Ctxt.Cont.t) Effect.t
  | Log_enter_ctor :
      enter_ctor
      -> (Prov.t * Ty.Ctor.t * Prov.t * Ty.Ctor.t * Ctxt.Cont.t) Effect.t
  | Log_enter_ctor_arg :
      enter_ctor_arg
      -> (Ty.t * Ty.t * Variance.t Located.t * Ctxt.Cont.t) Effect.t

let request_fresh_ty_params n = Effect.perform (Request_fresh_ty_params n)
let ask_up ~of_ ~at = Effect.perform (Ask_up { of_; at })
let ask_ty_param_variances ctor = Effect.perform (Ask_ty_param_variances ctor)

let log_enter_refinement ~ty_test ~ty_scrut ~ctxt_cont =
  Effect.perform (Log_enter_refinement { ty_test; ty_scrut; ctxt_cont })
;;

let log_enter_ty ~ty_test ~ty_scrut ~ctxt_cont =
  Effect.perform (Log_enter_ty { ty_test; ty_scrut; ctxt_cont })
;;

let log_enter_existential_scrut prov_scrut ty_exists ty_test ctxt_cont =
  Effect.perform
    (Log_enter_existential_scrut { prov_scrut; ty_exists; ty_test; ctxt_cont })
;;

let log_enter_existential_test ty_scrut prov_test ty_exists ctxt_cont =
  Effect.perform
    (Log_enter_existential_test { ty_scrut; prov_test; ty_exists; ctxt_cont })
;;

let log_enter_union_scrut prov_scrut tys_scrut ty_test ctxt_cont =
  Effect.perform
    (Log_enter_union_scrut { prov_scrut; tys_scrut; ty_test; ctxt_cont })
;;

let log_enter_union_test ty_scrut prov_test tys_test ctxt_cont =
  Effect.perform
    (Log_enter_union_test { ty_scrut; prov_test; tys_test; ctxt_cont })
;;

let log_enter_inter_scrut prov_scrut tys_scrut ty_test ctxt_cont =
  Effect.perform
    (Log_enter_inter_scrut { prov_scrut; tys_scrut; ty_test; ctxt_cont })
;;

let log_enter_inter_test ty_scrut prov_test tys_test ctxt_cont =
  Effect.perform
    (Log_enter_inter_test { ty_scrut; prov_test; tys_test; ctxt_cont })
;;

let log_enter_top_level_generic_scrut prov_scrut name_scrut ty_test ctxt_cont =
  Effect.perform
    (Log_enter_top_level_generic_scrut
       { prov_scrut; name_scrut; ty_test; ctxt_cont })
;;

let log_enter_top_level_generic_test ty_scrut prov_test name_test ctxt_cont =
  Effect.perform
    (Log_enter_top_level_generic_test
       { ty_scrut; prov_test; name_test; ctxt_cont })
;;

let log_enter_ctor prov_scrut ctor_scrut prov_test ctor_test ctxt_cont =
  Effect.perform
    (Log_enter_ctor { prov_scrut; ctor_scrut; prov_test; ctor_test; ctxt_cont })
;;

let log_enter_ctor_arg ty_scrut ty_test variance ctxt_cont =
  Effect.perform (Log_enter_ctor_arg { ty_scrut; ty_test; variance; ctxt_cont })
;;

let log_exit elem (ty_rfmt, ty_param_rfmt_opt) =
  Effect.perform (Log_exit { elem; ty_rfmt; ty_param_rfmt_opt })
;;

let log_exit_refinement = log_exit Refinement
let log_exit_ty = log_exit Ty
let log_exit_existential_scrut = log_exit (Exists Scrut)
let log_exit_existential_test = log_exit (Exists Test)
let log_exit_union_scrut = log_exit @@ Union Scrut
let log_exit_union_test = log_exit @@ Union Test
let log_exit_inter_scrut = log_exit @@ Inter Scrut
let log_exit_inter_test = log_exit @@ Inter Test
let log_exit_top_level_generic_scrut = log_exit @@ Top_level_generic Scrut
let log_exit_top_level_generic_test = log_exit @@ Top_level_generic Test
let log_exit_ctor = log_exit Ctor
let log_exit_ctor_arg = log_exit Ctor_arg

let run comp src oracle =
  let src_ref = ref src in
  Effect.Deep.match_with
    comp
    ()
    { effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Log_exit { ty_rfmt; ty_param_rfmt_opt; _ } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty_rfmt, ty_param_rfmt_opt))
          | Log_enter_refinement { ty_test; ty_scrut; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont))
          | Log_enter_ty { ty_test; ty_scrut; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty_test, ty_scrut, ctxt_cont))
          | Log_enter_existential_scrut
              { prov_scrut; ty_exists; ty_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue
                  k
                  (prov_scrut, ty_exists, ty_test, ctxt_cont))
          | Log_enter_existential_test
              { ty_scrut; prov_test; ty_exists; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue
                  k
                  (ty_scrut, prov_test, ty_exists, ctxt_cont))
          | Log_enter_union_scrut { prov_scrut; tys_scrut; ty_test; ctxt_cont }
            ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue
                  k
                  (prov_scrut, tys_scrut, ty_test, ctxt_cont))
          | Log_enter_union_test { ty_scrut; prov_test; tys_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty_scrut, prov_test, tys_test, ctxt_cont))
          | Log_enter_inter_scrut { prov_scrut; tys_scrut; ty_test; ctxt_cont }
            ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue
                  k
                  (prov_scrut, tys_scrut, ty_test, ctxt_cont))
          | Log_enter_inter_test { ty_scrut; prov_test; tys_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty_scrut, prov_test, tys_test, ctxt_cont))
          | Log_enter_top_level_generic_scrut
              { prov_scrut; name_scrut; ty_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue
                  k
                  (prov_scrut, name_scrut, ty_test, ctxt_cont))
          | Log_enter_top_level_generic_test
              { ty_scrut; prov_test; name_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue
                  k
                  (ty_scrut, prov_test, name_test, ctxt_cont))
          | Log_enter_ctor
              { prov_scrut; ctor_scrut; prov_test; ctor_test; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue
                  k
                  (prov_scrut, ctor_scrut, prov_test, ctor_test, ctxt_cont))
          | Log_enter_ctor_arg { ty_scrut; ty_test; variance; ctxt_cont } ->
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k (ty_scrut, ty_test, variance, ctxt_cont))
          | Request_fresh_ty_params n ->
            let offset = !src_ref in
            src_ref := offset + n;
            let names =
              List.init n ~f:(fun i ->
                Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset))
            in
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k names)
          | Ask_up { of_; at } ->
            let inst = Oracle.up oracle ~of_ ~at in
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k inst)
          | Ask_ty_param_variances ctor ->
            let ty_param_vars_opt = Oracle.param_variances_opt oracle ~ctor in
            Some
              (fun (k : (a, _) Effect.Deep.continuation) ->
                Effect.Deep.continue k ty_param_vars_opt)
          | _ -> None)
    ; retc = (fun res -> res, !src_ref)
    ; exnc = (fun exn -> raise exn)
    }
;;
