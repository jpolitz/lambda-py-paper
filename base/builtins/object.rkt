#lang plai-typed/untyped

;; object - the base-class of everything
(require "../python-core-syntax.rkt" 
         "../util.rkt"
         "type.rkt"
         "num.rkt"
         "str.rkt"
         (typed-in racket/base (string-length : (string -> number))))

(define object-class
  (seq-ops (list
             (CAssign (CId 'object (GlobalId))
                      (builtin-class
                        'object
                        (list)
                        (CNone)))

             (def 'object '__new__
                  (CFunc (list 'cls) (some 'args)
                         (CReturn (CObject (CId 'cls (LocalId)) (none)))
                         (some 'object)))

             (def 'object '__init__ 
                  (CFunc (list 'self) (none)
                         (CId 'self (LocalId))
                         (some 'object)))

             (def 'object '__eq__
                  (CFunc (list 'self 'other) (none)
                         (CReturn (CBuiltinPrim 'Is
                                    (list
                                          (CId 'self (LocalId))
                                          (CId 'other (LocalId)))))
                         (some 'object)))

             (def 'object '__str__ 
                  (CFunc (list 'self)  (none)
                         (CReturn (CBuiltinPrim 'obj-str (list (CId
                                                                 'self (LocalId)))))
                         (some 'object)))

             (def 'object '__cmp__
                  (CFunc (list 'self 'other) (none)
                         (CReturn (CIf (CBuiltinPrim 'Is
                                          (list
                                               (CId 'self (LocalId))
                                               (CId 'other (LocalId))))
                                       (make-builtin-num 0)
                                       (make-builtin-num -1)))
                         (some 'object)))

             (def 'object '__bool__
                  (CFunc (list) (some 'self)
                         (CReturn (CTrue))
                         (some 'object)))

             (def 'object '__gt__
                  (CFunc (list 'self 'other) (none)
                         (CLet '_cmpresult (LocalId)
                               (py-app (py-getfield (CId 'self (LocalId)) '__cmp__)
                                     (list (CId 'other (LocalId)))
                                     (none))
                               (CReturn (py-app (py-getfield (CId '_cmpresult (LocalId)) '__gt__)
                                              (list (make-builtin-num 0))
                                              (none))))
                         (some 'object)))
             (def 'object '__lt__
                  (CFunc (list 'self 'other) (none)
                         (CLet '_cmpresult (LocalId)
                               (py-app (py-getfield (CId 'self (LocalId)) '__cmp__)
                                     (list (CId 'other (LocalId)))
                                     (none))
                               (CReturn (py-app (py-getfield (CId '_cmpresult (LocalId)) '__lt__)
                                              (list (make-builtin-num 0))
                                              (none))))
                         (some 'object)))
             (def 'object '__lte__
                  (CFunc (list 'self 'other) (none)
                         (CLet '_cmpresult (LocalId)
                               (py-app (py-getfield (CId 'self (LocalId)) '__cmp__)
                                     (list (CId 'other (LocalId)))
                                     (none))
                               (CReturn (py-app (py-getfield (CId '_cmpresult (LocalId))
                                                         '__lte__)
                                              (list (make-builtin-num 0))
                                              (none))))
                         (some 'object)))
             (def 'object '__iter__
                  (CFunc (list 'self) (none)
                         (CReturn (py-app (py-getfield (CId 'SeqIter (LocalId)) '__init__)
                                        (list (CId 'self (LocalId)))
                                        (none)))
                         (some 'object)))
             (def 'object '__gte__
                  (CFunc (list 'self 'other) (none)
                         (CLet '_cmpresult (LocalId)
                               (py-app (py-getfield (CId 'self (LocalId)) '__cmp__)
                                     (list (CId 'other (LocalId)))
                                     (none))
                               (CReturn (py-app (py-getfield (CId '_cmpresult (LocalId))
                                                         '__gte__)
                                              (list (make-builtin-num 0))
                                              (none))))
                         (some 'object))))))


;; produces true-val if the object is truthy and false-val if it is not
(define (truthy-object? [o : CVal]) : boolean
  (if (some? (VObjectClass-mval o))
      (let ([mval (some-v (VObjectClass-mval o))])
        (type-case MetaVal mval
          [MetaNum (n) (if (= n 0) false true)]
          [MetaStr (s) (if (= (string-length s) 0) false true)]
                 [MetaList (v) (if (= (length v) 0) false true)]
                 [MetaTuple (v) (if (= (length v) 0) false true)]
                 [MetaDict (contents) (if (= (length (hash-keys contents)) 0) false true)]
                 [MetaNone () false]
                 [else true]))
   true))

(define (metaval->string [mval : (optionof MetaVal)])
  (if (some? mval)
      (type-case MetaVal (some-v mval)
        [MetaNone () ":none"]
        [MetaNum (n) ":num"]
        [MetaStr (s) ":str"]
        [MetaList (v) ":list"]
        [MetaTuple (v) ":tuple"]
        [MetaSet (elts) ":set"]
        [MetaDict (c) ":dict"]
        [MetaClass (c) ":class"]
        [MetaClosure (env args vararg body cls) ":closure"]
        [MetaCode (e filename globals) ":code"]
        [MetaPort (p) ":port"])
      ""))

(define (obj-str (args : (listof CVal)) env sto) : (optionof CVal)
  (local [(define o (first args))]
         (type-case CVal o
            [VObjectClass (ante mval d class)
                     (some (VObject 'str
                        (if (and (some? mval) (MetaClass? (some-v mval)))
                            (some (MetaStr (string-append "<class "
                                           (string-append (symbol->string
                                                            (MetaClass-c (some-v mval)))
                                                          ">"))))
                            (some (MetaStr
                                    (string-append "<instance of " 
                                                   (string-append 
                                                     (if (symbol=? ante 'none)
                                                       "Object"
                                                       (symbol->string ante))
                                                     (string-append (metaval->string mval)
                                                                    ">"))))))
                        (hash empty)))]
            [else (error 'obj-str "Non object")])))

(define (obj-getattr (args : (listof CVal)) env sto) : (optionof CVal)
  (if (= (length args) 2)
      (type-case CVal (first args)
        [VObjectClass (_ __ the-dict ___)
          (type-case CVal (second args)
            [VObjectClass (_ mval __ ___)
              (type-case MetaVal (some-v mval)
                [MetaStr (the-field)
                  (type-case (optionof Address) (hash-ref
                                                 the-dict
                                                 (string->symbol the-field))
                    [some (w) (some (fetch-once w sto))]
                    [none () (none)])]
                [else (none)])]
            [else (none)])]
        [else (none)])
      (none)))
