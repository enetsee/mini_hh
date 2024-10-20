open Core
module Ctxt = Ctxt
module Cstr = Cstr
module Err = Err
module Prop = Prop

module Eager_leftmost_dfs = struct
  let rec tell_prop prop ~ctxt =
    match prop with
    | Prop.Atom cstr -> tell_cstr cstr ~ctxt
    | Prop.Disj props -> tell_any props ~errs:[] ~ctxt
    | Prop.Conj props -> tell_all props ~errs:[] ~ctxt

  and tell_cstr cstr ~ctxt =
    match cstr with
    | Cstr.Is_subtype is_subtype ->
      (match Is_subtype.step is_subtype ~ctxt with
       | Ok prop -> tell_prop prop ~ctxt
       | Error err -> Some err)

  and tell_all props ~errs ~ctxt =
    match props with
    | [] when List.is_empty errs -> None
    | [] -> Some (Err.conj errs)
    | next :: rest ->
      let errs =
        match tell_prop next ~ctxt with
        | Some err -> err :: errs
        | None -> errs
      in
      tell_all rest ~errs ~ctxt

  and tell_any props ~errs ~ctxt =
    match props with
    | [] -> Some (Err.disj errs)
    | next :: rest ->
      (match tell_prop next ~ctxt with
       | Some err -> tell_any rest ~errs:(err :: errs) ~ctxt
       | None -> None)
  ;;
end

module Tell = struct
  let all props ~ctxt = Eager_leftmost_dfs.tell_all props ~errs:[] ~ctxt
  let any props ~ctxt = Eager_leftmost_dfs.tell_any props ~errs:[] ~ctxt
  let one cstr ~ctxt = Eager_leftmost_dfs.tell_cstr cstr ~ctxt
  let is_subtype ~ty_sub ~ty_super ~ctxt = one (Cstr.is_subtype ~ty_sub ~ty_super) ~ctxt
end
