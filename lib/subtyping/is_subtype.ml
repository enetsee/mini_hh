let step Cstr.Is_subtype.{ ty_sub; ty_super } ~ctxt:_ =
  let open Ty.Node in
  match Ty.(prj ty_sub, prj ty_super) with
  (* ~~ C-Top ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | _, (_, Inter []) -> Ok Prop.true_
  | (_prov_sub, Inter []), (_prov_super, _) -> Error (Err.not_a_subtype ~ty_sub ~ty_super)
  (* ~~ C-Bot ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  | (_prov_sub, Base b1), (_prov_super, Base b2) ->
    if Common.Base.equal b1 b2 then Ok Prop.true_ else Error (Err.not_a_subtype ~ty_sub ~ty_super)
  | _, _ -> Ok Prop.true_
;;
(* -- C-Top -------------------------------------------------------------------------------------------------------
      | _, Ty.Inter (ts, _) when Set.is_empty ts -> return @@ Ok Prop.true_
      | Ty.Inter (ts, pr_sub), _ when Set.is_empty ts ->
        return @@ Error (Err.Not_a_subtype (Prov.flow ~from:pr_sub ~into:(Ty.prov_of ty_sup)))
      (* -- C-Bot ------------------------------------------------------------------------------------------------------- *)
      | Ty.Union (ts, _), _ when Set.is_empty ts -> return @@ Ok Prop.true_
      | _, Ty.Union (ts, pr_sup) when Set.is_empty ts ->
        let pr_sub = Ty.prov_of ty_sub in
        return @@ Error (Err.Not_a_subtype (Prov.flow ~from:pr_sub ~into:pr_sup)) *)
