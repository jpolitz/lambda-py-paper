#lang plai-typed/untyped

(require
  redex
  "../base/python-core-syntax.rkt"
  "lambdapy-core.rkt")

(define (core->redex core-stx)
  (local [
    (define (mval->redex mval)
      (type-case MetaVal mval
        [MetaStr (s) (term (meta-str ,s))]
        [else (error 'mval->redex "NYI")]))
  ]
  (type-case CExpr core-stx
    [CSym (s) (term (sym ,(symbol->string s)))]
    [CTrue () (term true)]
    [CFalse () (term false)]
    [CNone () (term none)]
    [CClass (name) (term (class x))]
    [CObject (class mval)
     (term (object ,(core->redex class) ,(mval->redex mval)))]
    [else (error 'core-to-redex "NYI")])))
#|
    [CGetField (value : CExpr) (attr : symbol)]
    [CSeq (e1 : CExpr) (e2 : CExpr)]
    [CAssign (target : CExpr) (value : CExpr)]
    [CIf (test : CExpr) (then : CExpr) (else : CExpr)]
    [CId (x : symbol) (type : IdType)]
    [CLet (x : symbol) (type : IdType) (bind : CExpr) (body : CExpr)]
    [CApp (fun : CExpr) (args : (listof CExpr)) (stararg : (optionof CExpr))]
    [CFunc (args : (listof symbol)) (varargs : (optionof symbol)) (body : CExpr) (opt-class : (optionof symbol))] ; class name for methods
    [CWhile (test : CExpr) (body : CExpr) (orelse : CExpr)]
    [CReturn (value : CExpr)]
    [CPrim1 (prim : symbol) (arg : CExpr)]
    [CPrim2 (prim : symbol) (arg1 : CExpr) (arg2 : CExpr)]
    [CBuiltinPrim (op : symbol) (args : (listof CExpr))]
    [CList (class : CExpr) (values : (listof CExpr))]
    [CTuple (class : CExpr) (values : (listof CExpr))]
    [CSet (class : CExpr) (values : (listof CExpr))]
    [CRaise (expr : (optionof CExpr))]
    [CTryExceptElse (try : CExpr) (exn-id : symbol) (excepts : CExpr) (orelse : CExpr)]
    [CTryFinally (try : CExpr) (finally : CExpr)]
    [CUndefined]
    [CBreak]
    [CContinue]
    [CModule (prelude : CExpr) (body : CExpr)]
    [CConstructModule (source : CExpr)])
|#
