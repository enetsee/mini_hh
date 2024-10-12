open Core
module Ctxt = Ctxt
module State = State
module Cstr = Cstr
module Err = Err
module Prop = Prop

module Eager_leftmost_dfs = struct
  let rec tell_prop prop ~ctxt ~state =
    match prop with
    | Prop.Atom cstr -> tell_cstr cstr ~ctxt ~state
    | Prop.Disj props -> tell_any props ~errs:[] ~ctxt ~state
    | Prop.Conj props -> tell_all props ~errs:[] ~ctxt ~state

  and tell_cstr cstr ~ctxt ~state =
    match cstr with
    | Cstr.Is_subtype is_subtype ->
      (match Is_subtype.step is_subtype ~ctxt ~state with
       | Ok (prop, state) -> tell_prop prop ~ctxt ~state
       | Error err -> Error err)

  and tell_all props ~errs ~ctxt ~state =
    match props with
    | [] when List.is_empty errs -> Ok state
    | [] -> Error (Err.conj errs)
    | next :: rest ->
      let errs, state =
        match tell_prop next ~ctxt ~state with
        | Error err -> err :: errs, state
        | Ok env -> errs, env
      in
      tell_all rest ~errs ~ctxt ~state

  and tell_any props ~errs ~ctxt ~state =
    match props with
    | [] -> Error (Err.disj errs)
    | next :: rest ->
      (match tell_prop next ~ctxt ~state with
       | Error err -> tell_any rest ~errs:(err :: errs) ~ctxt ~state
       | Ok env -> Ok env)
  ;;
end

module Tell = struct
  let all props ~ctxt ~state = Eager_leftmost_dfs.tell_all props ~errs:[] ~ctxt ~state
  let any props ~ctxt ~state = Eager_leftmost_dfs.tell_any props ~errs:[] ~ctxt ~state
  let one cstr ~ctxt ~state = Eager_leftmost_dfs.tell_cstr cstr ~ctxt ~state
  let is_subtype ~ty_sub ~ty_super ~ctxt ~state = one (Cstr.is_subtype ~ty_sub ~ty_super) ~ctxt ~state
end
