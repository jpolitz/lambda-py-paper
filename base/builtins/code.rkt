#lang plai-typed/untyped

(require "str.rkt"
         "tuple.rkt"
         "../util.rkt"
         "../python-core-syntax.rkt")

(define code-class : CExpr
  (seq-ops
   (list
    (CAssign (CId 'code (GlobalId))
             (builtin-class
              'code
              (list 'object)
              (CNone)))
    (def 'code 'get_globals
         (CFunc (list 'self) (none)
                (CReturn
                 (CBuiltinPrim 'code-globals
                               (list (CId 'self (LocalId)))))
                (some 'code)))
    (def 'code '__str__
         (CFunc (list 'self) (none)
                (CReturn
                 (CBuiltinPrim 'code-str
                               (list (CId 'self (LocalId)))))
                (some 'code))))))

(define (code-str (args : (listof CVal))
                  (env : Env)
                  (sto : Store)) : (optionof CVal)
   (check-types args env sto 'code
                (some (VObject 'str
                               (some (MetaStr
                                      (pretty-metaval mval1)))
                               (hash empty)))))

(define (code-globals (args : (listof CVal))
                      (env : Env)
                      (sto : Store)) : (optionof CVal)
   (check-types args env sto 'code
                (some (make-builtin-tuple
                       (map
                        (lambda (name)
                          (make-str-value (symbol->string name)))
                        (MetaCode-globals mval1))))))