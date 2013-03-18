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
    (define (idtype->redex idtype)
      (type-case IdType idtype
        [LocalId () 'local]
        [GlobalId () 'global]))
  ]
  (type-case CExpr core-stx
    [CSym (s) (term (sym ,(symbol->string s)))]
    [CTrue () (term true)]
    [CFalse () (term false)]
    [CNone () (term none)]
    [CObject (class mval)
     (term (object ,(core->redex class) ,(mval->redex mval)))]
    [CGetField (value attr)
     (term (get-field ,(core->redex value) ,attr))]
    [CId (x type)
     (term (id ,x ,(idtype->redex type)))]
    [CSeq (e1 e2) (term (seq ,(core->redex e1) ,(core->redex e2)))]
    [CAssign (target value)
     (term (assign ,(core->redex target) ,(core->redex value)))]
    [CIf (test then els)
     (term (if ,(core->redex test) ,(core->redex then) ,(core->redex els)))]
    [CLet (x type bind body)
     (term (let (,x ,(idtype->redex type) ,(core->redex bind))
      ,(core->redex body)))]
    [CApp (fun args stararg)
     (term (app ,(core->redex fun)
                ,(map core->redex args)
                ,(core->redex stararg)))]
    ;; TODO(joe): all combinations
    [CFunc (args varargs body opt-class)
     (term (fun ,args ,(core->redex body) ,(core->redex opt-class)))]
    [CWhile (test body orelse)
     (term (while ,(core->redex test)
                  ,(core->redex body)
                  ,(core->redex orelse)))]
    [CReturn (value) (term (return ,(core->redex value)))]
    [CBuiltinPrim (op args)
     (term (builtin-prim ,op ,(map core->redex args)))]
    [CList (class values)
     (term (list ,(core->redex class) ,(map core->redex values)))]
    [CTuple (class values)
     (term (tuple ,(core->redex class) ,(map core->redex values)))]
    [CSet (class values)
     (term (set ,(core->redex class) ,(map core->redex values)))]
    [CRaise (expr)
     (term (raise ,(core->redex expr)))]
    [CTryExceptElse (try exn-id excepts orelse)
     (term (tryexcept ,(core->redex try) ,exn-id
                      ,(core->redex excepts)
                      ,(core->redex orelse)))]
    [CTryFinally (try finally)
     (term (tryfinally ,(core->redex try)
                       ,(core->redex finally)))]
    [CBreak () (term break)]
    [CContinue () (term continue)]
    [CUndefined () (term undefined)]
    [CModule (prelude body)
     (term (module ,(core->redex prelude) ,(core->redex body)))]
    [CConstructModule (source)
     (term (construct-module ,(core->redex source)))])))
