%{
  open Core
  open Reporting
  open Common
  open Lang
  open Helpers
%}

(* ~~ Keywords ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

%token<Reporting.Span.t> 
  SCRIPT_MARKER
  CLASS INTERFACE TRAIT REQUIRE EXTENDS IMPLEMENTS USE ABSTRACT FINAL
  AS SUPER
  STATIC PUBLIC PRIVATE
  FUNCTION OPTIONAL RETURN WHERE
  CONST CASE TYPE NEWTYPE SHAPE
  IF ELSE
  SOME ALL
  IS 
  LET
  BOOL INT FLOAT STRING THIS ARRAYKEY NUM NONNULL MIXED NOTHING

  // NEW 
  // WHILE DO FOR FOREACH BREAK CONTINUE SWITCH DEFAULT EXIT
  // PROTECTED ENUM SHAPE 

(* ~~ Symbols & punctuation ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

%token<Reporting.Span.t> 
  LPAREN RPAREN LBRACE RBRACE LANGLE RANGLE COLON QUESTION ELLIPSIS PLUS MINUS
  COMMA DOT AMPERSAND PIPE EQUAL LOGICAL_AND LOGICAL_OR SEMICOLON DOUBLE_ARROW
  LLANGLE RRANGLE 

  // UNDERSCORE
  // MUL DIV IS_EQUAL IS_NOT_EQUAL IS_IDENTICAL 
  // IS_NOT_IDENTICAL IS_LESS_THAN_OR_EQUAL IS_GREATER_THAN_OR_EQUAL 
  // BANG LBRACKET RBRACKET
  // LONG_DOUBLE_ARROW QUESTION_ARROW 
  // 

(* ~~ Literals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
%token<Reporting.Span.t>  NULL 
%token<Reporting.Span.t>  TRUE
%token<Reporting.Span.t>  FALSE
%token <string * Reporting.Span.t> LNUMBER   (* integer number 42 (LNUMBER) *)
%token <string * Reporting.Span.t > DNUMBER   (* floating-point number 42.00 (DNUMBER) *)
%token <string * Reporting.Span.t> CONSTANT_ENCAPSED_STRING

(* ~~ Names & Locals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
%token<Reporting.Span.t>  IDENT_THIS 
%token<string * Reporting.Span.t>
  IDENT 
  LOCAL

(* ~~ End states ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

%token EOF                      

(* ~~ Precedence & associativity ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


%nonassoc LPAREN 
// %left QUESTION
// %left PIPE
// %left AMPERSAND
// %right DOUBLE_ARROW LONG_DOUBLE_ARROW 
// %left EQUAL 
// %nonassoc ARROW QUESTION_ARROW LBRACKET
// %nonassoc LPAREN LBRACE
// %left AS
%left LOGICAL_OR
%left LOGICAL_AND
%left IS AS 
%right LLANGLE
// %nonassoc IS_EQUAL IS_NOT_EQUAL IS_IDENTICAL
// %right IS_NOT_IDENTICAL
// %right RANGLE
// %nonassoc IS_LESS_THAN_OR_EQUAL IS_GREATER_THAN_OR_EQUAL
// %left PLUS MINUS DOT 
// %left MUL DIV MOD
// %right BANG
// %left pre_ELSE
// %left ELSE

%start<Lang.Prog.t> program
%%

(* ~~ Rules ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* ~~ Programs are lists of top-level definitions ~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

program: SCRIPT_MARKER? defs=list(toplevel_def) EOF { Prog.{defs} };


toplevel_def:
  | class_def { Def.classish $1 }
  | intf_def { Def.classish $1 }
  | trait_def { Def.classish $1 }
  | type_def { Def.ty $1 }
  | fn_def { Def.fn $1 }
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
      let elem = Classish_def.Kind.class_ ~is_abstract ~is_final in
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
      let elem = Classish_def.Kind.Intf in
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
      let elem = Classish_def.Kind.Intf in
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

(* ~~ statements ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

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
   | prefix=if_without_else ELSE else_=statement_if { 
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



(* ~~ expressions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

expr: (* Expr.t  *)
  | open_expr(expr) { $1 }
  | span_start=LPAREN e=expr span_end=RPAREN {
    let span = Span.join span_start span_end in
    Located.with_span e ~span
  }
;

open_expr(left):
  | ctor=left LLANGLE ty_arg_spans=nonempty_comma_list(ty_expr) span_end=RRANGLE {
    let ty_args = List.map ~f:fst ty_arg_spans in
    let span = 
      let span_start = Located.span_of ctor in 
      Span.join span_start span_end
    in
    let apply = Lang.Apply.create ~ctor ~ty_args () in
    let elem = Expr_node.Apply apply in
    Located.create ~elem ~span ()
  }
  | lit_span=lit {
    let (lit,span) = lit_span in
    let elem = Expr_node.Lit lit in 
    Located.create ~elem ~span ()
  }
  // | span_start=NEW ty_ctor_name fn_args {}
  | span=IDENT_THIS {
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
  | IDENT { 
    let (str,span) = $1 in
    let elem = Expr_node.Ident  (Name.Fn.of_string str) in
    Located.create ~elem ~span ()
  }
  | func=left LPAREN call_args=comma_list_trailing(call_arg) span_end=RPAREN { 
    let span = 
      let span_start = Located.span_of func in 
      Span.join span_start span_end
    in
    let args , unpacked_arg = build_call_args call_args in
    let call = Call.create ~func  ~args ?unpacked_arg () in
    let elem = Expr_node.Call call in
    Located.create ~elem ~span ()
  }
;  

call_arg: 
  | expr { `Normal $1 } 
  | span_start=ELLIPSIS expr=expr { 
    let Located.{elem;span} = expr in
    let span = Span.join span span_start in
    let expr = Located.create ~elem ~span () in
    `Unpacked expr 
  }
;


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

  | span=NULL {
     let prov = Prov.witness span in 
     Ty.null prov , span
  } 
  | span=NONNULL {
     let prov = Prov.witness span in 
     Ty.nonnull prov , span
  } 
  | span=MIXED {
     let prov = Prov.witness span in 
     Ty.mixed prov , span
  } 
  | span=NOTHING {
     let prov = Prov.witness span in 
     Ty.nothing prov , span
  } 
  | span=BOOL{
     let prov = Prov.witness span in 
     Ty.bool prov , span
  } 
  | span=INT{
     let prov = Prov.witness span in 
     Ty.int prov , span
  } 
  | span=FLOAT {
     let prov = Prov.witness span in 
     Ty.float prov , span
  } 
  | span=STRING {
     let prov = Prov.witness span in 
     Ty.string prov , span
  } 
  | span=ARRAYKEY {
     let prov = Prov.witness span in 
     Ty.arraykey prov , span
  } 
  | span=NUM {
     let prov = Prov.witness span in 
     Ty.num prov , span
  } 
  | span=THIS{
     let prov = Prov.witness span in 
     Ty.this prov , span
  } 
  | located_shape=ty_shape {
    let (shape,span) = located_shape in
    let node = Ty.Node.shape shape in
    let prov = Prov.witness span in 
    Ty.create ~node ~prov (), span
  }
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
  | quants_span=ty_forall_quants ty_span=ty_expr {
    let body, span_end = ty_span in
    let quants, span_start = quants_span in
    let span = Span.join span_start span_end in
    let prov = Prov.witness span in
    Ty.forall prov ~quants ~body, span
  }
;

ty_shape: (* Ty.Shape.t * Span.t *)
  | span_start=SHAPE LPAREN elems=nonempty_comma_list_trailing(ty_shape_field) span_end=RPAREN {
    let elem = build_shape elems in  
    let span = Span.join span_start span_end in 
    elem , span
  }
;

ty_shape_field: (* [`Required of Shape_field_label.t * Ty.t | `Optional of Shape_field_label.t * Ty.t | `Variadic of Ty.t] *)
  | label_span=shape_field_label DOUBLE_ARROW ty_span=ty_expr {
    let label,_label_span=label_span
    and ty,_ty_span = ty_span in 
    `Required(label,ty) 
  }
  | QUESTION label_span=shape_field_label DOUBLE_ARROW ty_span=ty_expr {
    let label,_label_span=label_span
    and ty,_ty_span = ty_span in 
    `Optional(label,ty) 
  }
  | ty_span_opt=ty_expr? span=ELLIPSIS {
    let ty = 
      match ty_span_opt with
      | Some (ty,_) -> ty
      | _ -> Ty.mixed (Prov.witness span) 
    in
    `Variadic ty
  }
;

shape_field_label: (* Shape_field_label.t * Span.t *)
  | str_span=CONSTANT_ENCAPSED_STRING {
    let str,span = str_span in
    let lbl = Name.Shape_field_label.of_string str in
    (Ty.Shape_field_label.lit lbl, span)
  }

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

ty_forall_quants: 
 | span_start=ALL quants=nonempty_comma_list(ty_quantifier) span_end=DOT {
  let span = Span.join span_start span_end in
  quants, span
 }

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
 | name=ty_ctor_name {
    let (name,span) = name in 
    let elem = Ty.Ctor.create ~name ~args:[] () in 
   elem , span 

 }
 | name=ty_ctor_name LANGLE args=nonempty_comma_list_trailing(ty_expr) span_end=RANGLE  {
    let (name,span_start) = name in 
    let span = Span.join span_start span_end in
    let args = List.map ~f:fst args in
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



(* ~~ Type definitions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

type_def: (* Lang.Ty_def.t Located.t *)
  | kind=type_def_kind name_span=ty_ctor_name 
    ty_params_opt=ty_param_defs? 
    cstrs=type_def_bound* 
    EQUAL  
    defs=type_def_rhs 
    span_end=SEMICOLON { 
      let span = 
        let span_start = Located.span_of kind in
        Span.join span_start span_end
      in
      let name = 
        let elem , span = name_span in
        Located.create ~elem ~span () 
      in
      let bounds = 
       ty_param_bounds_of_constraints cstrs in 
      let ty_params = 
        match ty_params_opt with
        | None -> []
        | Some (xs,_) -> xs
      in
      let elem = 
        Lang.Ty_def.create ~kind ~name ~ty_params ~bounds ~defs ()
      in
      Located.create ~elem ~span ()
  } 

type_def_rhs :
  | PIPE defs=lseparated_list(PIPE,type_def_rhs_elem) { defs }
  | def=type_def_rhs_elem  { [def] }

type_def_kind: (* Type_def.Kind.t Located.t *)
  | span_start=CASE span_end=TYPE  { 
    let span = Span.join  span_start span_end in
    Located.create ~elem:Lang.Ty_def.Kind.Case ~span ()
  }
  | span=NEWTYPE { Located.create ~elem:Lang.Ty_def.Kind.New ~span () }
  | span=TYPE { Located.create ~elem:Lang.Ty_def.Kind.Alias ~span () }


type_def_rhs_elem : (*  Ty.t * Ctxt.Ty_param.t *) 
  | ty_span=ty_expr where_constraints_opt=where_constraints? { 
    let (ty,_) = ty_span in
    let where_constraints = Option.value ~default:[] where_constraints_opt in
    ty , where_constraints
  }

type_def_bound: (* Lang.Ty_param_bound_def.t Located.t *)
  | span_start=AS ty_span=ty_expr { 
    let ty,span_end= ty_span in
    let span = Span.join span_start span_end 
    and elem = Lang.Ty_param_bound_def.As ty in
    Located.create ~elem ~span ()
  }
  | span_start=SUPER ty_span=ty_expr {
    let ty,span_end= ty_span in
    let span = Span.join span_start span_end 
    and elem = Lang.Ty_param_bound_def.Super ty in
    Located.create ~elem ~span ()
  }


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