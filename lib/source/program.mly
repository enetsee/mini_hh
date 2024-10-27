%{
  open Core
  open Reporting
  open Common
  open Lang


  let build_tuple_like elems ~ctor = 
    let rec aux elems ~k  = 
      match elems with
      | `Required elem :: rest -> 
        aux rest ~k:(fun ~required ~optional ~variadic -> 
        let required = elem::required in
        k ~required ~optional ~variadic)
      | `Optional elem :: rest -> 
        aux rest ~k:(fun ~required ~optional ~variadic -> 
        let optional = elem::optional in
        k ~required ~optional ~variadic)
      | `Variadic elem :: _ ->  
         k ~required:[] ~optional:[] ~variadic:(Some elem)
      | [] -> k ~required:[] ~optional:[] ~variadic:None 
    in
    aux elems ~k:ctor 

  let build_tuple tys = 
    build_tuple_like tys 
    ~ctor:(fun ~required ~optional ~variadic -> Ty.Tuple.create ~required ~optional ?variadic ())

  let build_fn_param_defs param_defs = 
    build_tuple_like param_defs 
    ~ctor:(fun ~required ~optional ~variadic -> Fn_param_defs.create ~required ~optional ?variadic ())

  let build_class_kind mods = 
    let rec aux mods is_abstract is_final span =
      match mods , is_abstract, is_final , span with
      | `Abstract span :: rest , None , None , None ->
         aux rest (Some span) None (Some span) 
      | `Abstract _ :: rest , Some _, None , _ -> 
        aux rest is_abstract is_final span
      | `Abstract _ :: rest , Some _, Some _ , _ -> 
        (is_abstract,is_final,span)
      | `Final span :: rest , None , None , None ->
         aux rest None (Some span) (Some span) 
      | `Final _ :: rest , Some _, None , _ -> 
        aux rest is_abstract is_final span
      | `Final _ :: rest , Some _, Some _ , _ -> 
        (is_abstract,is_final,span)
      | [] , _ , _ ,_ -> is_abstract, is_final , span 
    in
    aux mods None None None
     

  let ty_param_bounds_of_constraints (cstrs: Ty_param_bound_def.t Located.t list) =
    let rec aux cstrs ~k = 
      match cstrs with
      | [] -> k ([],[]) ([],[])
      | Located.{elem = Ty_param_bound_def.As upper;span} :: rest -> 
        aux rest ~k:(fun (lowers,span_lower) (uppers,span_upper) -> 
        k (lowers, span_lower) (upper::uppers, span::span_upper ))
      | Located.{elem = Ty_param_bound_def.Super lower;span} :: rest -> 
        aux rest ~k:(fun (lowers,span_lower) (uppers,span_upper) -> 
        k (lower::lowers, span :: span_lower) (uppers, span_upper))
    in
    aux cstrs ~k:(fun (lowers,span_lowers) (uppers,span_uppers) -> 
      let lower = Ty.union ~prov:(Prov.witnesses span_lowers) lowers
      and upper = Ty.inter ~prov:(Prov.witnesses span_uppers) uppers in
      Ty.Param_bounds.create ~lower ~upper ()
    )

  let ty_param_bounds_of_where_constraints (where_constraints: (Name.Ty_param.t Located.t * Ty_param_bound_def.t Located.t) list) = 
    let rec aux acc = function
     | [] -> Map.to_alist acc
     | (Located.{elem;span},bound)::rest -> 
       let acc = Map.add_multi acc ~key:elem ~data:(span,bound) in
       aux acc rest
    in
    List.map ~f:(fun (elem, span_cstrs) -> 
      let spans , cstrs = List.unzip span_cstrs in
      let span = List.hd_exn spans in
      let param_bounds =  ty_param_bounds_of_constraints cstrs in
      let name = Located.create ~elem ~span () in
      Ty.Param.create ~name ~param_bounds () 
  ) 
    @@ aux Name.Ty_param.Map.empty where_constraints

  let unzip_class_elems elems = 
    let rec aux elems ~k = 
      match elems with
      | [] -> k ([],[],[],[],[],[]) 
      | next::rest  -> 
        aux rest ~k:(fun (req_exts, req_impls, uses, methods,props, ty_consts)  ->
        match next with
       | `Require_extends elem -> 
         k @@ (elem::req_exts, req_impls, uses, methods,props,ty_consts) 
       | `Require_implements elem -> 
         k @@ (req_exts, elem::req_impls, uses, methods,props,ty_consts) 
       | `Use elem -> 
         k @@ (req_exts, req_impls, elem::uses, methods,props,ty_consts) 
       | `Method elem ->
         k @@ (req_exts, req_impls, uses, elem::methods,props,ty_consts) 
       | `Property elem -> 
         k @@ (req_exts, req_impls, uses, methods,elem::props,ty_consts) 
       | `Type_constant elem ->
         k @@ (req_exts, req_impls, uses, methods,props,elem::ty_consts) 
       )
  in
  aux elems ~k:(fun x -> x)
      
%}

(* ~~ Keywords ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

%token<Reporting.Span.t> 
  NEW CLASS INTERFACE TRAIT REQUIRE EXTENDS IMPLEMENTS USE ABSTRACT FINAL
  AS SUPER
  STATIC PUBLIC PRIVATE
  FUNCTION OPTIONAL RETURN WHERE
  CONST TYPE
  IF ELSE
  SOME 
  IS 
  LET

  // WHILE DO FOR FOREACH BREAK CONTINUE SWITCH CASE DEFAULT EXIT
  // PROTECTED NEWTYPE ENUM SHAPE 

(* ~~ Symbols & punctuation ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

%token<Reporting.Span.t> 
  LPAREN RPAREN LBRACE RBRACE LANGLE RANGLE COLON QUESTION ELLIPSIS PLUS MINUS
  COMMA DOT AMPERSAND PIPE EQUAL LOGICAL_AND LOGICAL_OR SEMICOLON UNDERSCORE

  // MUL DIV IS_EQUAL IS_NOT_EQUAL IS_IDENTICAL
  // IS_NOT_IDENTICAL IS_LESS_THAN_OR_EQUAL IS_GREATER_THAN_OR_EQUAL 
  // BANG LBRACKET RBRACKET
  // DOUBLE_ARROW LONG_DOUBLE_ARROW QUESTION_ARROW 
  // 

(* ~~ Literals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
%token<Reporting.Span.t>  NULL 
%token<Reporting.Span.t>  TRUE
%token<Reporting.Span.t>  FALSE
%token <string * Reporting.Span.t> LNUMBER   (* integer number 42 (LNUMBER) *)
%token <string * Reporting.Span.t > DNUMBER   (* floating-point number 42.00 (DNUMBER) *)
%token <string * Reporting.Span.t> CONSTANT_ENCAPSED_STRING

(* ~~ Names & Locals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
%token<Reporting.Span.t>  THIS 
%token<string * Reporting.Span.t>
  IDENT 
  LOCAL

(* ~~ End states ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

%token EOF                      

(* ~~ Precedence & associativity ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


// %nonassoc LPAREN 
// %left QUESTION
// %left PIPE
// %left AMPERSAND
// %right DOUBLE_ARROW LONG_DOUBLE_ARROW 
// %left EQUAL 
// %nonassoc ARROW QUESTION_ARROW LBRACKET
// %nonassoc LPAREN LBRACE
%left IS AS 
// %left AS
%left LOGICAL_OR
%left LOGICAL_AND
// %nonassoc IS_EQUAL IS_NOT_EQUAL IS_IDENTICAL
// %right IS_NOT_IDENTICAL
// %right LANGLE
// %right RANGLE
// %nonassoc IS_LESS_THAN_OR_EQUAL IS_GREATER_THAN_OR_EQUAL
// %left PLUS MINUS DOT 
// %left MUL DIV MOD
// %right BANG
// %left pre_ELSE
// %left ELSE

%start<Lang.Def.t list> program
%%

(* ~~ Rules ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* ~~ Programs are lists of top-level definitions ~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

program: defs=list(toplevel_def) EOF { defs };


toplevel_def:
  | class_def { Def.classish $1 }
  | intf_def { Def.classish $1 }
  | trait_def { Def.classish $1 }
//   | type_def  { Def.ty $1  }
  | fn_def    { Def.fn $1 }
;

(* ~~ Class, interface & trait definitions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

class_def: (* Classish_def.t Located.t *)
  | mods=class_modifier* span_class=CLASS name=ty_ctor_name ty_params_opt=ty_param_defs?
    extends=preceded(EXTENDS,ty_ctor)?
    implements_opt=preceded(IMPLEMENTS, comma_list(ty_ctor))? 
    LBRACE class_elems=class_elem* span_end=RBRACE
  { 
    let (is_abstract,is_final,span_start_opt) = build_class_kind mods in 
    let span_start = Option.value ~default:span_class span_start_opt in
    let kind = 
      let span = Span.join span_start span_class in
      let elem = Classish_kind.class_ ~is_abstract ~is_final in
      Located.create ~elem ~span ()
    in
    let span = Span.join span_start span_end in
    let elem = 
      let (name,span) = name in
      let name = Located.create ~elem:name ~span () in
      let locate (elem,span) = Located.create ~elem ~span () in 
      let extends = Option.map ~f:locate extends in
      let ty_params = Option.value_map  ~default:[] ~f:fst ty_params_opt in
      let implements = Option.value_map ~default:[] ~f:(List.map ~f:locate) implements_opt in
      let ( require_extends
        , require_implements
        , uses
        , methods
        , properties
        , ty_consts
        ) = unzip_class_elems class_elems in
      Classish_def.create ~kind ~name ~ty_params ?extends ~implements 
        ~require_extends ~require_implements ~uses ~methods ~properties 
        ~ty_consts ()
    in  
    Located.create ~elem ~span ()
   }
;

class_modifier: 
  | ABSTRACT { `Abstract $1}
  | FINAL { `Final $1}

intf_def: (* Classish_def.t Located.t *)
  | span_start=INTERFACE name=ty_ctor_name ty_params_opt=ty_param_defs?
    extends_opt=preceded(EXTENDS, comma_list(ty_ctor))? 
    LBRACE class_elem* span_end=RBRACE 
  {
    let span = Span.join span_start span_end in
    let kind = 
      let elem = Classish_kind.Intf in
      Located.create ~elem ~span:span_start ()
    in
    let elem = 
      let (name,span) = name in
      let locate (elem,span) = Located.create ~elem ~span () in 
      let name = Located.create ~elem:name ~span () in
      let ty_params = Option.value_map  ~default:[] ~f:fst ty_params_opt in
      let implements = Option.value_map ~default:[] ~f:(List.map ~f:locate) extends_opt in
      Classish_def.create ~kind ~name ~ty_params ~implements ()
    in
    Located.create ~elem ~span ()  
  }
;


trait_def: (* Classish_def.t Located.t *)
  | span_start=TRAIT name=ty_ctor_name ty_params_opt=ty_param_defs?
    implements_opt=preceded(IMPLEMENTS, comma_list(ty_ctor))? 
    LBRACE class_elem* span_end=RBRACE
  { 
    let span = Span.join span_start span_end in
    let kind = 
      let elem = Classish_kind.Intf in
      Located.create ~elem ~span:span_start ()
    in
    let elem = 
      let (name,span) = name in
      let locate (elem,span) = Located.create ~elem ~span () in 
      let name = Located.create ~elem:name ~span () in
      let ty_params = Option.value_map  ~default:[] ~f:fst ty_params_opt in
      let implements = Option.value_map ~default:[] ~f:(List.map ~f:locate) implements_opt in
      Classish_def.create ~kind ~name ~ty_params ~implements ()
    in
    Located.create ~elem ~span () 
   }
;

class_elem:
  | span_start=USE ty_ctor_span=ty_ctor span_end=SEMICOLON { 
    let elem = fst ty_ctor_span 
    and span = Span.join span_start span_end in
    `Use (Located.create ~elem ~span ())
  }
  | span_start=REQUIRE EXTENDS ty_ctor_span=ty_ctor span_end=SEMICOLON {
    let elem = fst ty_ctor_span 
    and span = Span.join span_start span_end in
    `Require_extends (Located.create ~elem ~span ())
  }
  | span_start=REQUIRE IMPLEMENTS ty_ctor_span=ty_ctor span_end=SEMICOLON {
    let elem = fst ty_ctor_span 
    and span = Span.join span_start span_end in
    `Require_implements (Located.create ~elem ~span ())
  }
  | visibility=visibility static_opt=STATIC? fn_def=fn_def {
    let span_start =  Located.span_of visibility in
    let static_or_instance = 
      Option.value_map static_opt ~default:Static_or_instance.Instance 
      ~f:(fun span -> Static_or_instance.static span) 
    in
    let Located.{elem=fn_def;span=span_end} = fn_def in
    let span = Span.join span_start span_end in
    let elem = Method_def.create ~visibility ~static_or_instance ~fn_def () in
    `Method (Located.create ~elem ~span ())
  }
  | visibility=visibility static_opt=STATIC? ty_span=ty_expr str_span=LOCAL default_value=property_suffix span_end=SEMICOLON {
    let span_start =  Located.span_of visibility in
    let static_or_instance = 
      Option.value_map static_opt ~default:Static_or_instance.Instance 
      ~f:(fun span -> Static_or_instance.static span) 
    in 
    let ty = fst ty_span in
    let name = 
      let str,span = str_span in
      let elem = Name.Tm_var.of_string str in
      Located.create ~elem ~span ()
    in
    let span = Span.join span_start span_end 
    and elem = Property_def.create ~name ~visibility ~static_or_instance ~ty ?default_value () in
    `Property (Located.create ~elem ~span ())
  }
  | ty_const=ty_const { `Type_constant ty_const }

ty_const:
  | span_start=ABSTRACT CONST TYPE name=ty_param_name  cstrs=ty_param_constraints span_end=SEMICOLON {
    let bounds = ty_param_bounds_of_constraints cstrs in 
    let span = Span.join span_start span_end 
    and elem = Ty_const_def.create ~name ~bounds () in
    Located.create ~elem ~span ()
  }
  | span_start=CONST TYPE name=ty_param_name EQUAL ty_span=ty_expr span_end=SEMICOLON {
    let ty = fst ty_span in 
    let span = Span.join span_start span_end 
    and elem = Ty_const_def.create_equal name ty  in
    Located.create ~elem ~span ()
  }
;

property_suffix:
  | (* empty *) { None  }
  | EQUAL expr=expr { Some expr }
;

visibility:
  | span=PUBLIC {
    let elem = Visibility.Public in
    Located.create ~elem ~span ()
  }
  | span=PRIVATE {
    let elem = Visibility.Public in
    Located.create ~elem ~span ()
  }
;
(* ~~ Function definitions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

fn_def: (* Fn_def.t Located.t *)
| span_start=FUNCTION name=fn_name ty_params_span_opt=ty_param_defs?
    span_params_start=LPAREN params=fn_param_defs RPAREN return_span=return_ty
    where_constraints_opt=where_constraints?
    LBRACE stmts=statement* span_end=RBRACE {
  let span = Span.join span_start span_end in
  let (ty_params,sig_span_start) = Option.value ~default:([],span_params_start) ty_params_span_opt in
  (* *)
  let return = fst return_span in
  let lambda_sig =  
    let span=  
      Span.join (snd return_span) sig_span_start in
    let elem = Lambda_sig.create ~ty_params ~params ~return () in
    Located.create ~elem ~span ()
  in
  let body = 
    Seq.Seq stmts in
  let lambda = 
    Lambda.create ~lambda_sig ~body () 
  in
  let where_constraints = Option.value ~default:[] where_constraints_opt in
  let elem  = Fn_def.create ~name ~lambda ~where_constraints () in
  Located.create ~elem ~span ()
}

fn_name: (* Name.Fn.t Located.t *)
  | IDENT { 
    let (str,span) = $1 in
    let elem = Name.Fn.of_string str in
    Located.create ~elem ~span ()
  }
;


fn_param_defs: (* Fn_param_defs.t *)
  | params=comma_list_trailing(fn_param_def) {
     build_fn_param_defs params
  }
;

fn_param_def: (* Fn_param_def.t Located.t *)
  |  ty_span=ty_expr str_span=LOCAL default_arg_opt=preceded(EQUAL, expr)?  { 
    let param = 
      let (ty,span_start) = ty_span in
      let (str,span_end) = str_span in
      let name = 
        let elem = Name.Tm_var.of_string str in 
        Located.create ~elem ~span:span_end () 
      in
      let elem = Fn_param_def.create ~ty ~name () in 
      let span = Span.join span_start span_end in
      Located.create ~span ~elem ()
    in
    
    match default_arg_opt with
    | Some expr -> 
       `Optional (param,expr)
    | _ -> `Required param 
  }
  | ty_span=ty_expr span_start=ELLIPSIS str_span=LOCAL { 
    let (ty,span_start) = ty_span in
    let (str,span_end) = str_span in
    let name = 
      let span = Span.join span_start span_end in
      let elem = Name.Tm_var.of_string str in 
      Located.create ~span ~elem () 
    in
    let elem = Fn_param_def.create ~ty ~name () in 
    let span = Span.join span_start span_end in
    `Variadic (Located.create ~elem ~span () )
  }
;

(* ~~ statements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

statement:
  | span=SEMICOLON { 
    let elem = Stmt_node.noop in 
    Located.create ~elem ~span () 
  }
  | e=expr span_end=SEMICOLON {
    let span_start = Located.span_of e in
    let span = Span.join span_start span_end in
    let elem = Stmt_node.Expr e in
    Located.create ~span ~elem () 
  }
  | span_start=RETURN e_opt=expr? span_end=SEMICOLON {
    let span = Span.join span_start span_end in
    let elem = Stmt_node.Return e_opt in
    Located.create ~span ~elem () 
  }
  | lvalue=lvalue EQUAL rhs=expr span_end=SEMICOLON {
    let assign= Assign.create ~lvalue ~rhs () in
    let elem = Stmt_node.Assign assign in
    let span_start = Located.span_of lvalue in
    let span = Span.join span_start span_end in
    Located.create ~elem ~span ()
  }
  | span_start=LET LBRACE ty_params=nonempty_comma_list(ty_param_name) COMMA 
    str_span=LOCAL RBRACE EQUAL rhs=expr span_end=SEMICOLON {
    let tm_var = 
    let str , span = str_span in
    let elem = Name.Tm_var.of_string str in
    Located.create ~elem ~span () in
    let unpack = Unpack.create ~tm_var ~ty_params ~rhs () in
    let elem = Stmt_node.Unpack unpack in
    let span = Span.join span_start span_end in 
    Located.create ~elem ~span ()
  }
  | seq { $1 }
  | statement_if { $1 }
;

seq: 
 | span_start=LBRACE stmts=statement* span_end=RBRACE {
   let span = Span.join span_start span_end in
   let seq = Seq.Seq stmts in
   let elem = Stmt_node.Seq seq in
   Located.create ~elem ~span ()
 }
;

statement_if:
  | prefix=if_without_else { 
    let (cond,then_,span_start) = prefix in
    let span_end = Located.span_of then_ in
    let span = Span.join span_start span_end in
    let else_ = 
      let elem = Stmt_node.noop in 
      Located.create ~elem ~span:span_end () 
    in
    let node = If.create ~cond ~then_ ~else_ () in
    let elem = Stmt_node.If node in
    Located.create ~elem ~span ()
   }
  | prefix=if_without_else ELSE else_=seq { 
    let (cond,then_,span_start) = prefix in
    let span_end = Located.span_of else_ in
    let span = Span.join span_start span_end in
    let node = If.create ~cond ~then_ ~else_ () in
    let elem = Stmt_node.If node in
    Located.create ~elem ~span ()
   }
;

if_without_else:
  | span_start=IF LPAREN cond=expr RPAREN then_=seq{ (cond,then_,span_start) }
;



(* ~~ expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

expr: (* Expr.t  *)
  | open_expr(expr) { $1 }
  | span_start=LPAREN e=expr span_end=RPAREN {
    let span = Span.join span_start span_end in
    Located.with_span e ~span
  }
;

open_expr(left):
  | lit_span=lit {
    let (lit,span) = lit_span in
    let elem = Expr_node.Lit lit in 
    Located.create ~elem ~span ()
  }
  // | span_start=NEW ty_ctor_name fn_args {}

  | span=THIS {
    Located.create ~elem:Expr_node.This ~span ()
  }
  | str_span=LOCAL {
    let (str,span) = str_span in 
    let name = Name.Tm_var.of_string str in
    let elem = Expr_node.Local name in
    Located.create ~elem ~span ()
  } 
  | scrut=left IS ty_span=ty_expr {
    let (ty_test,span_end) = ty_span in
    let span_start = Located.span_of scrut in
    let span = Span.join span_start span_end in
    let node = Is.create ~scrut ~ty_test () in
    let elem = Expr_node.Is node in
    Located.create ~elem ~span ()
  }
  | scrut=left AS ty_span=ty_expr {
    let (ty_assert,span_end) = ty_span in
    let span_start = Located.span_of scrut in
    let span = Span.join span_start span_end in
    let node = As.create ~scrut ~ty_assert () in
    let elem = Expr_node.As node in
    Located.create ~elem ~span ()
  }
  | lhs=left LOGICAL_AND rhs=expr {
    let span_start = Located.span_of lhs
    and span_end= Located.span_of rhs in
    let span = Span.join span_start span_end in
    let node = Binary.create ~lhs ~rhs ~binop:Binop.and_ () in
    let elem = Expr_node.Binary node in 
    Located.create ~elem ~span ()
  }
  | lhs=left LOGICAL_OR rhs=expr {
    let span_start = Located.span_of lhs
    and span_end= Located.span_of rhs in
    let span = Span.join span_start span_end in
    let node = Binary.create ~lhs ~rhs ~binop:Binop.or_ () in
    let elem = Expr_node.Binary node in 
    Located.create ~elem ~span ()
  }



lit: (* Lit.t * Span.t *) 
  | str_span=LNUMBER  {
    let str,span = str_span in
    (Lit.lnum str, span)
  }
  | str_span=DNUMBER  {
    let str,span = str_span in
    (Lit.dnum str, span)
  }
  | str_span=CONSTANT_ENCAPSED_STRING {
    let str,span = str_span in
    (Lit.const_string str, span)
  }
  | span=NULL { Lit.null , span}
  | span=TRUE  { Lit.bool true, span}
  | span=FALSE { Lit.bool false, span}


// lambda: 
//  | ty_params_opt=ty_param_defs?
//     LPAREN comma_list_trailing(parameter) RPAREN return_type? 
//     where_constraints?
//     LBRACE statement_inner* RBRACE {} 


(* ~~ L-values ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

lvalue:
 | str_span=LOCAL {
    let (str,span) = str_span in 
    let name = Name.Tm_var.of_string str in
    let elem = Lvalue.Local name in
    Located.create ~elem ~span ()
 }


(* ~~ Type parameter definitions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

where_constraints: (* (Name.Ty_param.t Located.t * Ty.Param_bounds.t) list *)
  | WHERE cstrs=nonempty_comma_list(where_constraint) {
    ty_param_bounds_of_where_constraints cstrs
  }
;

where_constraint: (* Name.Ty_param.t Located.t * Ty_param_bound_def.t Located.t *)
  | name=ty_param_name AS ty_span=ty_expr { 
    let span_start = Located.span_of name in 
    let ty,span_end = ty_span in 
    let span = Span.join span_start span_end in
    let elem = Ty_param_bound_def.as_ ty in
    name, Located.create ~span ~elem () 
  }
  | name=ty_param_name SUPER ty_span=ty_expr {
    let span_start = Located.span_of name in 
    let ty,span_end = ty_span in 
    let span = Span.join span_start span_end in
    let elem = Ty_param_bound_def.super ty in
    name, Located.create ~span ~elem () 
  }


ty_param_defs: (* Ty_param_def.t list * Span.t *)
  | span_start=LANGLE params=comma_list_trailing(ty_param_def) span_end=RANGLE 
    { (params, Span.join span_start span_end) }
;

ty_param_def: (* Ty_param_def.t *)
  | var=ty_param_variance name_bounds=constrained_ty_param {
    let name ,param_bounds = name_bounds in 
    let variance = 
      let elem = fst var
      (* If we have now variance modifier use the location of the parameter name *)
      and span = Option.value ~default:(Located.span_of name) @@ snd var in
      Located.create ~elem ~span ()
    in 
    Ty_param_def.create ~name ~variance ~param_bounds ()
  }
;
  
constrained_ty_param: (* Name.Ty_param.t Located.t * Ty.Param_bounds.t *)
 | name=ty_param_name cstrs=ty_param_constraints  {
    let bounds = ty_param_bounds_of_constraints cstrs in
    name,bounds
  }
;

ty_param_variance:
  | (* empty *) { Variance.Inv, None}
  | span=PLUS   { Variance.Cov, Some span }
  | span=MINUS  { Variance.Contrav, Some span }
;

ty_param_name:  (* Name.Ty_param.t Located.t *)
  | IDENT { 
    let (str,span) = $1 in
    let elem = Name.Ty_param.of_string str in
    Located.create ~elem ~span ()
  }
;

ty_param_constraints: (* Ty_param_bound_def.t Located.t list *)
  | (* empty *) { [] }
  | acc=ty_param_constraints span_start=AS ty_span=ty_expr {
    let ty, span_end = ty_span in 
    let span = Span.join span_start span_end in
    let elem = Ty_param_bound_def.as_ ty in
    let next = Located.create ~span ~elem () in
    next::acc
  }
  | acc=ty_param_constraints span_start=SUPER ty_span=ty_expr {
    let ty, span_end = ty_span in 
    let span = Span.join span_start span_end in
    let elem = Ty_param_bound_def.super ty in
    let next = Located.create ~span ~elem () in
    next::acc
  }
;
 
(* ~~ Type expressions (hints) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)  

ty_expr: (* Ty.t * Span.t *)
  | simple_ty_expr { $1 }
  | span_start=LPAREN elem=binary_ty_expr span_end=RPAREN { 
     let span = Span.join span_start span_end in 
     let prov = Prov.witness span in
     let ty = 
       match elem with
       | `Union tys -> Ty.union ~prov tys
       | `Inter tys -> Ty.inter ~prov tys
    in
    ty, span
    }
;

binary_ty_expr:
  | union_ty_expr { `Union $1 }
  | inter_ty_expr { `Inter $1 }
;

inter_ty_expr: (* Ty.t list *)
  | tys=inter_ty_expr_aux { List.rev tys}
;

inter_ty_expr_aux:
   | ty_l=ty_expr AMPERSAND ty_r=ty_expr { 
    [fst ty_r;fst ty_l]
   }
  | tys=inter_ty_expr_aux AMPERSAND ty_r=ty_expr {
    (fst ty_r)::tys
  }
;

union_ty_expr: (* Ty.t list *)
  | tys=union_ty_expr_aux { List.rev tys }

union_ty_expr_aux:
   | ty_l=ty_expr PIPE ty_r=ty_expr { 
    [fst ty_r;fst ty_l]
   }
  | tys=union_ty_expr_aux PIPE ty_r=ty_expr {
    (fst ty_r)::tys
  }
;


simple_ty_expr: (* Ty.t * Span.t *)
  | located_ctor=ty_ctor { 
    let (ctor,span) = located_ctor in 
    let node = Ty.Node.ctor ctor in
    let prov = Prov.witness span in 
    Ty.create ~node ~prov (), span
  }
  | span_null=QUESTION ty_nonnull_span=ty_expr {
    let ty_null = Ty.null @@ Prov.witness span_null in
    let ty_nonnull,span_nonnull = ty_nonnull_span in
    let span = Span.join span_null span_nonnull in
    let prov = Prov.witness span in
    Ty.union ~prov [ty_null;ty_nonnull], span
  }
  | located_tuple=ty_tuple { 
    let (tuple,span) = located_tuple in 
    let node = Ty.Node.tuple tuple in
    let prov = Prov.witness span in 
    Ty.create ~node ~prov (), span
  }
  | span_start=LPAREN FUNCTION params=ty_fn_params return_span=return_ty span_end=RPAREN {
    let span = Span.join span_start span_end in
    let prov = Prov.witness span in
    let return = fst return_span in
    let fn = Ty.Fn.create ~params ~return () in
    let node = Ty.Node.fn fn in 
    Ty.create ~node ~prov (), span
  }
  | quants_span=ty_exists_quants ty_span=ty_expr {
    let body, span_end = ty_span in
    let quants, span_start = quants_span in
    let span = Span.join span_start span_end in
    let prov = Prov.witness span in
    Ty.exists prov ~quants ~body, span
  }
;

ty_tuple: (* Ty.Tuple.t * Span.t *)
  | span_start=LPAREN elems=nonempty_comma_list_trailing(ty_tuple_elem) span_end=RPAREN {
      let elem = build_tuple elems in 
      let span = Span.join span_start span_end in
      elem, span 
  }
;

ty_tuple_elem: (* [`Required of Ty.t | `Optional of Ty.t | `Variadic of Ty.t ]*)
  | ty_span=ty_expr { `Required (fst ty_span) }
  | OPTIONAL ty_span=ty_expr { `Optional (fst ty_span) }
  | ty_span=ty_expr ELLIPSIS { `Variadic (fst ty_span) }
;

ty_fn_params: (* Ty.Tuple.t *)
  | LPAREN RPAREN {
      build_tuple [] 
    }
  | located_tuple=ty_tuple { fst located_tuple }
;

return_ty: (* Ty.t * Span.t *)
  | COLON ty_expr { $2 }
;

ty_exists_quants: 
 | span_start=SOME quants=nonempty_comma_list(ty_quantifier) span_end=DOT {
  let span = Span.join span_start span_end in
  quants, span
 }

ty_quantifier:  (* Ty.Param.t *)
  | name=ty_param_name {
    let span = Located.span_of name in
    let prov = Prov.witness span in
    let param_bounds = Ty.Param_bounds.top prov in
    Ty.Param.create ~name ~param_bounds ()
  }
  | span_start=LPAREN name=ty_param_name cstrs=ty_param_constraints span_end=RPAREN {
    let span = Span.join span_start span_end in
    let prov = Prov.witness span in
    let param_bounds = ty_param_bounds_of_constraints cstrs in
    Ty.Param.create ~name ~param_bounds ()
  }

ty_ctor: (* Ty.Ctor.t * Span.t *)
 | name=ty_ctor_name args_span_opt=ty_args {
    let (name,span_start) = name in 
    let args,span_end_opt = args_span_opt in
    let span = Option.value_map ~default:span_start ~f:(Span.join span_start) span_end_opt in 
    let elem = Ty.Ctor.create ~name ~args () in
    elem , span 
  }
;

ty_ctor_name: (* Name.Ctor.t * Span.t *)
  | IDENT { 
    let (str,span) = $1 in
    let elem = Name.Ctor.of_string str in
    elem,span
  }
;

ty_args: (* Ty.t list, Span.t option *)
  | (* empty *) { [], None }
  | span_start=LANGLE elems=nonempty_comma_list_trailing(ty_expr) span_end=RANGLE { 
    (List.map ~f:fst elems , Some(Span.join span_start span_end))
  }
;


(* ~~ Generic definitions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

%inline lnonempty_list(X):
| X llist_aux(X) { $1 :: List.rev $2 }
;

%inline llist(X):
| llist_aux(X) { List.rev $1 }
;

llist_aux(X):
| (* empty *) { [] }
| llist_aux(X) X { $2 :: $1 }
;

%inline lseparated_list(sep, X):
| (* empty *) { [] }
| lseparated_nonempty_list(sep, X) { $1 }
;

%inline lseparated_list_trailing(sep, X):
| (* empty *) { [] }
| lseparated_nonempty_list(sep, X) sep? { $1 }
;

%inline lseparated_nonempty_list(sep, X):
| lseparated_nonempty_list_aux(sep, X) { List.rev $1 };
;

lseparated_nonempty_list_aux(sep, X):
| X { [$1] }
| lseparated_nonempty_list_aux(sep, X) sep X { $3 :: $1 }
;

%inline comma_list(X):
| lseparated_list(COMMA, X) { $1 }
;

%inline comma_list_trailing(X):
| lseparated_list_trailing(COMMA, X) { $1 }
;

%inline nonempty_comma_list(X):
| lseparated_nonempty_list(COMMA, X) { $1 }
;

%inline nonempty_comma_list_trailing(X):
| lseparated_nonempty_list(COMMA, X) COMMA? { $1 }
;