#lang plai-typed/untyped

(require
  redex
  "../base/python-core-syntax.rkt"
  "lambdapy-core.rkt")

(define (core->redex core-stx)
  (local [
    (define (var->redex/opt maybe-var)
      (type-case (optionof symbol) maybe-var
        [some (x) (term (,x))]
        [none () (term (no-var))]))
    (define (mval->redex mval)
      (type-case MetaVal mval
        [MetaNone () (term (meta-none))]
        [MetaNum (n) (term (meta-num ,n))]
        [MetaStr (s) (term (meta-str ,s))]
        [MetaClass (c) (term (meta-class ,c))]
        [else (error 'core->redex (string-append "Shouldn't be seeing this mval in surface output: " (to-string mval)))]))
    (define (mval->redex/opt maybe-mval)
      (type-case (optionof MetaVal) maybe-mval
        [some (m) (mval->redex m)]
        [none () (term (no-meta))]))
    (define (idtype->redex idtype)
      (type-case IdType idtype
        [LocalId () 'local]
        [GlobalId () 'global]))
    (define (core->redex/opt val)
      (type-case (optionof CExpr) val
        [some (e) (core->redex e)]
        [none () (term ())]))
  ]
  (type-case CExpr core-stx
    [CSym (s) (term (sym ,(symbol->string s)))]
    [CTrue () (term true)]
    [CFalse () (term false)]
    [CNone () (term none)]
    [CObject (class mval)
     (term (object ,(core->redex class) ,(mval->redex/opt mval)))]
    [CGetField (value attr)
     (term (get-field ,(core->redex value) ,(symbol->string attr)))]
    [CGetAttr (value attr)
     (term (get-attr ,(core->redex value) ,(core->redex attr)))]
    [CId (x type)
     (term (id ,x ,(idtype->redex type)))]
    [CSeq (e1 e2) (term (seq ,(core->redex e1) ,(core->redex e2)))]
    [CAssign (target value)
     (term (assign ,(core->redex target) := ,(core->redex value)))]
    [CIf (test then els)
     (term (if ,(core->redex test) ,(core->redex then) ,(core->redex els)))]
    [CLet (x type bind body)
     (let [(result (term (let (,x ,(idtype->redex type) = ,(core->redex bind)) in
      ,(core->redex body))))]
      (begin
        #;(display (string-append "Result of let: " (string-append (to-string (length result)) "\n\n")))
        result))]
    [CApp (fun args stararg)
     (type-case (optionof CExpr) stararg
      [some (e)
       (term (app ,(core->redex fun)
                  ,(map core->redex args)
                  ,(core->redex e)))]
      [none ()
       (term (app ,(core->redex fun)
                  ,(map core->redex args)))])]
    ;; TODO(joe): all combinations
    [CFunc (args varargs body opt-class)
     (term (fun ,args
                ,(var->redex/opt varargs)
                ,(core->redex body)
                ,(var->redex/opt opt-class)))]
    [CWhile (test body orelse)
     (term (while ,(core->redex test)
                  ,(core->redex body)
                  ,(core->redex orelse)))]
    [CReturn (value) (term (return ,(core->redex value)))]
    [CBuiltinPrim (op args)
     (prim->redex op args)]
    [CList (class values)
     (term (list ,(core->redex class) ,(map core->redex values)))]
    [CTuple (class values)
     (term (tuple ,(core->redex class) ,(map core->redex values)))]
    [CSet (class values)
     (term (set ,(core->redex class) ,(map core->redex values)))]
    [CRaise (expr)
     (term (raise ,(core->redex/opt expr)))]
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
     (term (construct-module ,(core->redex source)))]
    [CYield (e) (error 'core-to-redex "The Redex model doesn't know anything about CYield.  Use CPS to remove CYields before calling core-to-redex")])))

(define (prim-noalloc op args)
  (term (builtin-prim ,op ,args)))
(define (prim-alloc op args)
  (term (alloc (builtin-prim ,op ,args))))
(define (prim-update op to-update args)
  (term (set! ,to-update (builtin-prim ,op ,args))))

(define (prim->redex opsym args)
  (local [
    (define argvs (map (lambda (a) (term (fetch ,(core->redex a)))) args))
    (define argsptrs (map (lambda (a) (core->redex a)) args))
    (define op (symbol->string opsym))
  ]
  (case opsym
    ['num+ (prim-alloc op argvs)]
    [else (prim-noalloc op argsptrs)])))

