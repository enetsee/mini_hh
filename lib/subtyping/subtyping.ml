open Core
module Ctxt = Ctxt
module Cstr = Cstr
module Err = Err
module Prop = Prop
module Answer = Answer
module Eff = Eff
module State = State

module Eager_leftmost_dfs = struct
  let rec tell_prop prop ~ctxt_cont =
    let prop, ctxt_cont = Eff.log_enter_tell_prop prop ctxt_cont in
    Eff.log_exit_tell_prop
    @@
    match prop with
    | Prop.Atom cstr -> tell_cstr cstr ~ctxt_cont
    | Prop.Disj props -> tell_any props ~errs:[] ~ctxt_cont
    | Prop.Conj props -> tell_all props ~errs:[] ~ctxt_cont

  and tell_cstr cstr ~ctxt_cont =
    let cstr, ctxt_cont = Eff.log_enter_tell_cstr cstr ctxt_cont in
    Eff.log_exit_tell_cstr
    @@
    match cstr with
    | Cstr.Is_subtype { ty_sub; ty_super; polarity } ->
      (match Is_subtype.step ~ty_sub ~ty_super ~polarity ~ctxt_cont with
       | Ok (prop, ctxt_cont) -> tell_prop prop ~ctxt_cont
       | Error err -> Some err)
    | Cstr.Can_instantiate_with { ty; args } ->
      (match Can_instantiate_with.step ~ty ~args ~ctxt_cont with
       | Ok (prop, ctxt_cont) -> tell_prop prop ~ctxt_cont
       | Error err -> Some err)

  and tell_all props ~errs ~ctxt_cont =
    let props, errs, ctxt_cont = Eff.log_enter_tell_all props errs ctxt_cont in
    Eff.log_exit_tell_all
    @@
    match props with
    | [] when List.is_empty errs -> None
    | [] -> Some (Err.conj errs)
    | next :: rest ->
      let errs =
        match tell_prop next ~ctxt_cont with
        | Some err -> err :: errs
        | None -> errs
      in
      tell_all rest ~errs ~ctxt_cont

  and tell_any props ~errs ~ctxt_cont =
    let props, errs, ctxt_cont = Eff.log_enter_tell_any props errs ctxt_cont in
    Eff.log_exit_tell_any
    @@
    match props with
    | [] -> Some (Err.disj errs)
    | next :: rest ->
      (match tell_prop next ~ctxt_cont with
       | Some err -> tell_any rest ~errs:(err :: errs) ~ctxt_cont
       | None -> None)
  ;;
end

module Tell = struct
  let all props ~ctxt_cont =
    Eager_leftmost_dfs.tell_all props ~errs:[] ~ctxt_cont
  ;;

  let any props ~ctxt_cont =
    Eager_leftmost_dfs.tell_any props ~errs:[] ~ctxt_cont
  ;;

  let one cstr ~ctxt_cont = Eager_leftmost_dfs.tell_cstr cstr ~ctxt_cont

  let is_subtype ~ty_sub ~ty_super ~ctxt_cont =
    one (Cstr.is_subtype ~ty_sub ~ty_super) ~ctxt_cont
  ;;

  let can_instantiate_with ~ty ~args ~ctxt_cont =
    one (Cstr.can_instantiate_with ~ty ~args) ~ctxt_cont
  ;;
end

module Ask = struct
  let is_subtype ~ty_sub ~ty_super ~ctxt_cont =
    (* We don't have tyvars yet so this is the same... *)
    match Tell.is_subtype ~ty_sub ~ty_super ~ctxt_cont with
    | Some err -> Answer.No err
    | _ -> Answer.Yes
  ;;
end
