open Core

let synth local ~env =
  (* Find the type of the term variable and any refinements *)
  match Envir.Typing.(find_local env local, find_local_refinement env local) with
  | None, _ -> Error (Err.unbound_local local)
  | Some ty, _refinement_opt ->
    (* TODO(mjt) apply refinements *)
    Ok ty
;;
(* Ok (Option.value_map ~default:ty ~f:(fun refinement -> Ty.refine ty refinement) refinement_opt) *)
