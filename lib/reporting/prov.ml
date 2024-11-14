open Core

type t =
  | Empty
  | Witness of Witness.t
  | Flow of flow
  | Prj_both of
      { inner : t
      ; prj : Projection.Symm.t
      ; sub : t
      ; super : t
      }
  | Prj_one of
      { inner : t
      ; outer : t
      ; prj : Projection.Asymm.t
      }
  | Axiom of
      { prev : t
      ; next : t
      ; axiom : Axiom.t
      }

and flow =
  | Refine of
      { scrut : t
      ; test : t
      }
  | Unpack of
      { packed : t
      ; unpacked : t
      }
  | Assign of
      { rhs : t
      ; lvalue : t
      }
  | Use of
      { def : t
      ; tm_var : t
      }
[@@deriving compare, eq, sexp, show, yojson]

let empty = Empty

(* ~~ Witness constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let witness span = Witness (Witness.witness span)
let witnesses spans = Witness (Witness.witnesses spans)
let lit_null span = Witness (Witness.lit_null span)
let lit_bool span = Witness (Witness.lit_bool span)
let lit_lnum span = Witness (Witness.lit_lnum span)
let lit_dnum span = Witness (Witness.lit_dnum span)
let lit_const_string span = Witness (Witness.lit_bool span)
let expr_is span = Witness (Witness.expr_is span)
let expr_as span = Witness (Witness.expr_as span)
let expr_if_cond span = Witness (Witness.expr_if_cond span)
let expr_tm_var span = Witness (Witness.expr_tm_var span)
let stmt_if_join span = Witness (Witness.stmt_if_join span)
let lvalue_tm_var span = Witness (Witness.lvalue_tm_var span)
let def_where_clause span = Witness (Witness.def_where_clause span)

(* ~~ Flow constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
let refine ~prov_test ~prov_scrut =
  Flow (Refine { scrut = prov_scrut; test = prov_test })
;;

let unpack ~prov_packed ~prov_unpacked =
  Flow (Unpack { packed = prov_packed; unpacked = prov_unpacked })
;;

let assign ~prov_rhs ~prov_lvalue =
  Flow (Assign { rhs = prov_rhs; lvalue = prov_lvalue })
;;

let use ~prov_def ~prov_tm_var =
  Flow (Use { def = prov_def; tm_var = prov_tm_var })
;;

(* ~~ Projection constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let prj_asymm_sub ~sub ~sub_prj prj =
  Prj_one { inner = sub_prj; prj; outer = sub }
;;

let prj_asymm_super ~super ~super_prj prj =
  Prj_one { inner = super_prj; prj; outer = super }
;;

let prj_union_sub ~sub ~sub_prj =
  prj_asymm_sub ~sub ~sub_prj Projection.Asymm.Union
;;

let prj_union_super ~super ~super_prj =
  prj_asymm_super ~super ~super_prj Projection.Asymm.Union
;;

let prj_inter_sub ~sub ~sub_prj =
  prj_asymm_sub ~sub ~sub_prj Projection.Asymm.Inter
;;

let prj_inter_super ~super ~super_prj =
  prj_asymm_super ~super ~super_prj Projection.Asymm.Inter
;;

(* ~~ Symmetric projections ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let prj_symm_co ~sub ~sub_prj ~super prj =
  Prj_both { inner = sub_prj; prj; sub; super }
;;

let prj_symm_contra ~sub ~super ~super_prj prj =
  Prj_both { inner = super_prj; prj; sub; super }
;;

let prj_nullable ~sub ~sub_prj ~super =
  prj_symm_co ~sub ~sub_prj ~super Projection.Symm.Nullable
;;

let prj_tuple ~sub ~sub_prj ~super ~idx_sub ~idx_super =
  let prj = Projection.Symm.Tuple { idx_sub; idx_super } in
  prj_symm_co ~sub ~sub_prj ~super prj
;;

let prj_ctor_co ~sub ~sub_prj ~super kind name idx is_invariant =
  let dir = Projection.Variance_dir.Cov in
  let cstr_variance =
    if is_invariant
    then Projection.Cstr_variance.Inv dir
    else Projection.Cstr_variance.Dir dir
  in
  let prj = Projection.Symm.Ctor { kind; name; idx; cstr_variance } in
  prj_symm_co ~sub ~sub_prj ~super prj
;;

let prj_ctor_contra ~sub ~super ~super_prj kind name idx is_invariant =
  let dir = Projection.Variance_dir.Contrav in
  let cstr_variance =
    if is_invariant
    then Projection.Cstr_variance.Inv dir
    else Projection.Cstr_variance.Dir dir
  in
  let prj = Projection.Symm.Ctor { kind; name; idx; cstr_variance } in
  prj_symm_contra ~sub ~super ~super_prj prj
;;

(* ~~ Axioms ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let axiom_extends ~child ~ancestor =
  Axiom { axiom = Axiom.Extends; prev = child; next = ancestor }
;;

let axiom_upper_bound ~bound ~of_ =
  Axiom { axiom = Upper_bound; prev = of_; next = bound }
;;

let axiom_lower_bound ~bound ~of_ =
  Axiom { axiom = Lower_bound; prev = of_; next = bound }
;;

(* let prj_shape ~sub ~sub_prj ~super lbl ~kind_sub ~kind_super =
   let prj = Prj_symm_shape (lbl, kind_sub, kind_super) in
   prj_symm_co ~sub ~sub_prj ~super prj
   ;;

   let prj_fn_param ~sub ~super ~super_prj ~idx_sub ~idx_super =
   let prj = Prj_symm_fn_param (idx_super, idx_sub) in
   prj_symm_contra ~sub ~super ~super_prj prj
   ;;

   let prj_fn_param_inout_co ~sub ~sub_prj ~super ~idx_sub ~idx_super =
   let prj = Prj_symm_fn_param_inout (idx_sub, idx_super, Co) in
   prj_symm_co ~sub ~sub_prj ~super prj
   ;;

   let prj_fn_param_inout_contra ~sub ~super ~super_prj ~idx_sub ~idx_super =
   let prj = Prj_symm_fn_param_inout (idx_super, idx_sub, Contra) in
   prj_symm_contra ~sub ~super ~super_prj prj
   ;;

   let prj_fn_ret ~sub ~sub_prj ~super =
   let prj = Prj_symm_fn_ret in
   prj_symm_co ~sub ~sub_prj ~super prj
   ;; *)
