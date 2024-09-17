open Core
module Ctxt = Ctxt
module Cstr = Cstr
module Err = Err
module Prop = Prop

module Eager_leftmost_dfs = struct
  let rec tell_prop prop ~ctxt ~env =
    match prop with
    | Prop.Atom cstr -> tell_cstr cstr ~ctxt ~env
    | Prop.Disj props -> tell_any props ~errs:[] ~ctxt ~env
    | Prop.Conj props -> tell_all props ~errs:[] ~ctxt ~env

  and tell_cstr cstr ~ctxt ~env =
    match cstr with
    | Cstr.Is_subtype is_subtype ->
      (match Is_subtype.step is_subtype ~ctxt ~env with
       | Ok (prop, env) -> tell_prop prop ~ctxt ~env
       | Error err -> Error err)

  and tell_all props ~errs ~ctxt ~env =
    match props with
    | [] when List.is_empty errs -> Ok env
    | [] -> Error (Err.conj errs)
    | next :: rest ->
      let errs, env =
        match tell_prop next ~ctxt ~env with
        | Error err -> err :: errs, env
        | Ok env -> errs, env
      in
      tell_all rest ~errs ~ctxt ~env

  and tell_any props ~errs ~ctxt ~env =
    match props with
    | [] -> Error (Err.disj errs)
    | next :: rest ->
      (match tell_prop next ~ctxt ~env with
       | Error err -> tell_any rest ~errs:(err :: errs) ~ctxt ~env
       | Ok env -> Ok env)
  ;;
end

module Tell = struct
  let all props ~ctxt ~env = Eager_leftmost_dfs.tell_all props ~errs:[] ~ctxt ~env
  let any props ~ctxt ~env = Eager_leftmost_dfs.tell_any props ~errs:[] ~ctxt ~env
  let one cstr ~ctxt ~env = Eager_leftmost_dfs.tell_cstr cstr ~ctxt ~env
  let is_subtype ~ty_sub ~ty_super ~ctxt ~env = one (Cstr.is_subtype ~ty_sub ~ty_super) ~ctxt ~env
end
