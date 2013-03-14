#lang plai-typed/untyped

(require "python-core-syntax.rkt")

(require [opaque-type-in racket/set [Set set?]])
(require
 (typed-in racket/string (string-join : ((listof string) string -> string)))
 (typed-in racket/base (hash-for-each : ((hashof 'a 'b) ('c 'd -> 'e) -> void)))
 (typed-in racket/base (hash->list : ((hashof 'a 'b)  -> (listof 'c))))
 (typed-in racket/base (number->string : (number -> string)))
 (typed-in racket/base (car : (('a * 'b)  -> 'a)))
 (typed-in racket/base (cdr : (('a * 'b)  -> 'b)))
 (typed-in racket/set (set? : ('a -> boolean)))
 (typed-in racket/set (set->list : (set? -> (listof 'a))))
 (typed-in racket/set (set : ( -> set?)))
 (typed-in racket/set (set-add : (set? 'a -> set?)))
 (typed-in racket/base (exact? : (number -> boolean)))
 
 )
(require [typed-in racket (format : (string 'a -> string))])
(require [typed-in racket (flatten : ((listof (listof 'a) ) -> (listof 'a)))])
(require [typed-in racket (remove-duplicates : ((listof 'a) -> (listof 'a)))])
(require [typed-in racket (memq : ('a (listof 'a) -> (listof 'a)))])
(require [typed-in racket (memf : (('a -> boolean) (listof 'a) -> (listof 'a)))])

(require (typed-in racket/pretty (pretty-print : ('a -> 'b))))

(require (typed-in racket (current-directory : (-> 'b))))
(require (typed-in racket (path->string : ('a -> 'b))))

(print-only-errors #t)

; a file for utility functions that aren't specific to python stuff
(define (pprint exp)
  (pretty-print exp))

; sys.path default value

(define default-builtin-module-paths
  (list "."
        (string-append
         (path->string (current-directory)) "../tests/modules/")))

(define (get-module-path)
  default-builtin-module-paths)

(define python-path "/usr/local/bin/python3.2")
(define (get-pypath)
  python-path)
(define (set-pypath p)
  (set! python-path p))

; lists->hash - given two parallel list produce a mutable hash mapping 
; values from one to values in the other
(define (lists->hash [l1 : (listof 'a)] [l2 : (listof 'b)]) : (hashof 'a 'b)
  (local [(define h (make-hash empty))]
    (begin
      (map2 (lambda (k v) (hash-set! h k v))
            l1 l2)
      h)))

(define (make-exception-class [name : symbol]) : CExpr
  (builtin-class
    name
    (list 'BaseException)
    (CNone)))

(define (assign [name : symbol] [expr : CExpr]) : CExpr
  (CAssign (CId name (GlobalId))
           expr))

(define (list-subtract [big : (listof 'a) ] [small : (listof 'a)] ) : (listof 'a)
  (local
   [(define (list-remove [l : (listof 'a) ] [e : 'a]) : (listof 'a)
      (local [(define (filter-expression [this-elem : 'a] ) : boolean (not (equal? e this-elem)))]
      (filter filter-expression l)))]
   (cond
    [(empty? big) empty]
    [(empty? small) big]
    [else (list-subtract (list-remove big (first small)) (rest small))])))

(define (contains-char? [str : string] [c : char] ) : boolean
  (not (empty? (filter (lambda (x) (char=? x c)) (string->list str)))))

(define (chr [str : string] ) : char
  (let ((strlist (string->list str)))
    (if (and (not (empty? strlist)) (empty? (rest strlist)))
        (first strlist)
        (error 'python-desugar:chr (format "cannot convert ~a into a single character" str)))))



(define (list-replace [i : number] [val : 'a] [l : (listof 'a)]) : (listof 'a)
  (cond
    [(empty? l) (error 'util "list-replace out of range")]
    [(= 0 i) (cons val (rest l))]
    [else (cons (first l) (list-replace (- i 1) val (rest l)))]))

(define (immutable-hash-copy h)
  (let ([r (hash empty)])
    (begin
      (hash-for-each h (lambda (k v) (set! r (hash-set r k v))))
      r)))

(define (seq-ops (ops : (listof CExpr))) : CExpr
  (cond 
    [(= 1 (length ops)) (first ops)]
    [else (CSeq (first ops) 
                (seq-ops (rest ops)))]))

(define (def (class : symbol) (name : symbol) (expr : CExpr)) : CExpr
  (CAssign (CGetField (CId class (GlobalId)) name) expr))

(define (VObject [antecedent : symbol] [mval : (optionof MetaVal)]
                 [dict : (hashof 'symbol Address)]) : CVal
  (VObjectClass antecedent mval dict (none)))


; Macro to match varargs
; Example:
;
; (match-varargs 'args
;   [() (CObject (gid '%num) (some (MetaNum 0)))]
;   [('a) (CId 'a (LocalId))]
;   [('a 'b) (CBuiltinPrim 'num+ (CId 'a (LocalId)) (CId 'b (LocalId)))])
;
(define-syntax (match-varargs x)
  (syntax-case x ()
    [(match-varargs 'args [vars body])
     #'(if-varargs 'args vars body)]
    [(match-varargs 'args [vars1 body1] [vars2 body2])
     #'(if-varargs 'args vars1 body1
                 (if-varargs 'args vars2 body2))]
    [(match-varargs 'args [vars1 body1] [vars2 body2] [vars3 body3])
     #'(if-varargs 'args vars1 body1
                 (if-varargs 'args vars2 body2
                             (if-varargs 'args vars3 body3)))]))

; Helper macro used in implementing match-varargs
(define-syntax (if-varargs x)
  (syntax-case x ()
    [(if-varargs 'args vars body)
     #'(if-varargs 'args vars body (make-exception 'TypeError "argument mismatch"))]
    [(if-varargs 'args () body else-part)
     #'(CIf ; Did we get 0 args?
        (CBuiltinPrim 'num= (list (py-len 'args) (py-num 0)))
        body
        else-part)]
    [(if-varargs 'args (a) body else-part)
     #'(CIf ; Did we get 1 args?
        (CBuiltinPrim 'num= (list (py-len 'args) (py-num 1)))
        (CLet a (LocalId) (py-getitem 'args 0)
              body)
        else-part)]
    [(if-varargs 'args (a b) body else-part)
     #'(CIf ; Did we get 2 args?
        (CBuiltinPrim 'num= (list (py-len 'args) (py-num 2)))
        (CLet a (LocalId) (py-getitem 'args 0)
              (CLet b (LocalId) (py-getitem 'args 1)
                    body))
        else-part)]))

(define-syntax (check-types-pred x)
  (syntax-case x ()
    [(check-types args env sto tpred1? body)
     (with-syntax ([mval1 (datum->syntax x 'mval1)])
       #'(let ([arg1 (first args)])
           (if (VObjectClass? arg1)
               (let ([mayb-mval1 (VObjectClass-mval arg1)])
                 (if (and (some? mayb-mval1)
                          (tpred1? (some-v (VObjectClass-mval arg1))))
                     (let ([mval1 (some-v mayb-mval1)])
                       body)
                     (none)))
               (none))))]
    [(check-types args env sto tpred1? tpred2? body)
     (with-syntax ([mval1 (datum->syntax x 'mval1)]
                   [mval2 (datum->syntax x 'mval2)])
       #'(let ([arg1 (first args)]
               [arg2 (second args)])
           (if (and (VObjectClass? arg1) (VObjectClass? arg2))
               (let ([mayb-mval1 (VObjectClass-mval arg1)]
                     [mayb-mval2 (VObjectClass-mval arg2)])
                 (if (and (some? mayb-mval1) (some? mayb-mval2)
                          (tpred1? (some-v (VObjectClass-mval arg1)))
                          (tpred2? (some-v (VObjectClass-mval arg2))))
                     (let ([mval1 (some-v mayb-mval1)]
                           [mval2 (some-v mayb-mval2)])
                       body)
                     (none)))
               (none))))]))

;; the copypasta here is bad but we aren't clever enough with macros
(define-syntax (check-types x)
  (syntax-case x ()
    [(check-types args env sto t1 body)
     (with-syntax ([mval1 (datum->syntax x 'mval1)])
       #'(let ([arg1 (first args)])
           (if (and (VObjectClass? arg1)
                    (object-is? arg1 t1 env sto))
               (let ([mayb-mval1 (VObjectClass-mval arg1)])
                 (if (some? mayb-mval1)
                     (let ([mval1 (some-v mayb-mval1)])
                       body)
                     (none)))
               (none))))]
    [(check-types args env sto t1 t2 body)
     (with-syntax ([mval1 (datum->syntax x 'mval1)]
                   [mval2 (datum->syntax x 'mval2)])
       #'(let ([arg1 (first args)]
               [arg2 (second args)])
           (if (and (VObjectClass? arg1) (VObjectClass? arg2)
                    (object-is? arg1 t1 env sto)
                    (object-is? arg2 t2 env sto))
               (let ([mayb-mval1 (VObjectClass-mval arg1)]
                     [mayb-mval2 (VObjectClass-mval arg2)])
                 (if (and (some? mayb-mval1) (some? mayb-mval2))
                     (let ([mval1 (some-v mayb-mval1)]
                           [mval2 (some-v mayb-mval2)])
                       body)
                     (none)))
               (none))))]
    [(check-types args env sto t1 t2 t3 body)
     (with-syntax ([mval1 (datum->syntax x 'mval1)]
                   [mval2 (datum->syntax x 'mval2)]
                   [mval3 (datum->syntax x 'mval3)])
       #'(let ([arg1 (first args)]
               [arg2 (second args)]
               [arg3 (third args)])
           (if (and (VObjectClass? arg1) (VObjectClass? arg2)
                    (VObjectClass? arg3)
                    (object-is? arg1 t1 env sto)
                    (object-is? arg2 t2 env sto)
                    (object-is? arg3 t3 env sto))
               (let ([mayb-mval1 (VObjectClass-mval arg1)]
                     [mayb-mval2 (VObjectClass-mval arg2)]
                     [mayb-mval3 (VObjectClass-mval arg3)])
                 (if (and (some? mayb-mval1) 
                          (some? mayb-mval2)
                          (some? mayb-mval3))
                     (let ([mval1 (some-v mayb-mval1)]
                           [mval2 (some-v mayb-mval2)]
                           [mval3 (some-v mayb-mval3)])
                       body)
                     (none)))
               (none))))]))

;; returns true if the given o is an object of the given class or somehow a
;; subclass of that one. Modified to look at __mro__ for multiple inheritance
;; and to use the class object instead of the class name.
;; Preseved for compatibility with check-types macro, it should be avoided for other uses.
(define (object-is? [o : CVal] [c : symbol] [env : Env] [s : Store]) : boolean
  (let ([obj-cls (get-class o env s)]
        [cls (fetch-once (some-v (lookup c env)) s)])
    (member cls (get-mro obj-cls (none) s))))

;; get-mro: fetch __mro__ field as a list of classes, filtered up to thisclass if given
;; and prepended with cls to avoid self reference in __mro__
(define (get-mro [cls : CVal] 
                 [thisclass : (optionof CVal)]
                 [sto : Store]) : (listof CVal)
  (type-case (optionof Address) (hash-ref (VObjectClass-dict (fetch-ptr cls sto)) '__mro__)
    [some (w) (let ([mro (cons cls (MetaTuple-v (some-v (VObjectClass-mval
                                                  (fetch-ptr (fetch-once w sto) sto)))))])
                (if (none? thisclass)
                    mro
                    (if (> (length
                             (filter (lambda (c) (eq? (fetch-ptr (some-v thisclass) sto)
                                                      (fetch-ptr c sto)))
                                     mro))
                           0)
                        (rest (memf (lambda (c) (eq? (fetch-ptr (some-v thisclass) sto)
                                                     (fetch-ptr c sto)))
                                    mro))
                        (error 'get-mro
                          (string-append
                            (format "No member ~a in class mro " (some-v thisclass))
                              (to-string mro))))))]
    [none () (error 'get-mro (string-append "class without __mro__ field " 
                                            (pretty cls)))]))

;; option-map: unwrap the option, perform the function (if applicable), re-wrap.
(define (option-map [fn : ('a -> 'b)] [thing : (optionof 'a)]) : (optionof 'b)
    (type-case (optionof 'a) thing
          [some (v) (some (fn v))]
              [none () (none)]))

;; get-class: retrieve the object's class
(define (get-class [obj : CVal] [env : Env] [sto : Store]) : CVal
  (local ([define w_class (if (some? (VObjectClass-class obj))
                              (VObjectClass-class obj)
                              (some (fetch-once (some-v (lookup (VObjectClass-antecedent obj) env)) sto)))])
    (type-case (optionof CVal) w_class
      [some (cv) cv]
      [none () (error 'get-class (string-append "object without class " 
                                                (pretty obj)))])))


(define (is? [v1 : CVal]
             [v2 : CVal]
             [s : Store]) : boolean
  (begin
    ;(display v1) (display " ") (display v2) (display " ") (display (eq? v1 v2)) (display "\n")
    (or (eq? v1 v2)
        (and (is-obj-ptr? v1 s) (is-obj-ptr? v2 s)
             (eq? (fetch-ptr v1 s) (fetch-ptr v2 s))))))

(define (pretty arg)
  (type-case CVal arg
    [VObjectClass (a mval d class) (if (some? mval)
                            (pretty-metaval (some-v mval))
                            "Can't print non-builtin object.")]
    [VSym (s) (symbol->string s)]
    [VClosure (env args sarg body opt-class) "<function>"]
    [VUndefined () "Undefined"]
    [VPointer (a) (string-append "Pointer to address " (number->string a))]))

(define (pretty-metaval (mval : MetaVal)) : string
  (type-case MetaVal mval
    [MetaNum (n) (number->string n)]
    [MetaStr (s) s]
    [MetaClass (c) (string-append "<class "
                     (string-append (symbol->string c)
                                    ">"))]
    [MetaList (v) (string-append
                   (string-append "["
                                  (string-join (map pretty v) ", "))
                   "]")]
    [MetaTuple (v) (string-append
                   (string-append "("
                                  (string-join (map pretty v) ", "))
                   ")")]
    [MetaDict (contents)
              (string-append
              (string-append "{"
                             (string-join
                               (map (lambda (pair)
                                      (string-append (pretty (car pair))
                                        (string-append ": "
                                                       (pretty (cdr pair)))))
                                    (hash->list contents))
                               ", "))
              "}")]
    [MetaCode (e filename code)
              "<code object>"]
    [MetaNone () "None"]
    [MetaSet (elts)
              (string-append
              (string-append "{"
                             (string-join (map pretty (set->list elts)) ", "))
              "}")]
    [else "builtin-value"]
    ))

(define (pretty-exception [exnptr : CVal] [sto : Store] [print-name : boolean]) : string
  (local [(define exn (fetch-ptr exnptr sto))
          (define name (symbol->string (VObjectClass-antecedent exn)))
          (define args-loc (hash-ref (VObjectClass-dict exn) 'args))
          (define pretty-args (if (some? args-loc)
                                  (string-join 
                                    (map pretty
                                         (MetaTuple-v
                                           (some-v
                                             (VObjectClass-mval
                                               (fetch (some-v args-loc) sto)))))
                                    " ")
                                  ""))]
    (if print-name
        (if (not (string=? pretty-args ""))
            (string-append name 
                           (string-append ": "
                                          pretty-args))
            name)
        pretty-args)))

(define (make-exception [name : symbol] [error : string]) : CExpr
  (CApp
    (CId name (GlobalId))
    (list (make-builtin-str error))
    (none)))

(define (default-except-handler [id : symbol] [body : CExpr]) : CExpr
  (CIf (CApp (CId '%isinstance (GlobalId))
             (list (CId id (LocalId))
                   (CId 'BaseException (GlobalId)))
             (none))
       body
       (CId id (LocalId))))

; generates a new unique variable name that isn't allowed by user code 
(define new-id
  (let ([n (box 0)])
    (lambda ()
      (begin
        (set-box! n (add1 (unbox n)))
        (string->symbol (string-append (number->string (unbox n)) "var" ))))))

(define truedummy (VObjectClass 'bool (some (MetaNum 1)) (hash empty) (none)))
(define true-val truedummy)
(define (renew-true env sto)
  (if (or (VObjectClass? true-val)
          (and (is-obj-ptr? true-val sto)
               (VUndefined? (some-v (VObjectClass-class (fetch-ptr true-val sto))))))
      (local [(define with-class
                (VObjectClass 'bool (some (MetaNum 1)) (hash empty)
                              (some (fetch-once (some-v (lookup '%bool env)) sto))))
              (define new-true (alloc-result with-class sto))]
        (begin
          (set! true-val (v*s-v new-true))
          new-true))
      (v*s true-val sto)))

(define falsedummy (VObjectClass 'bool (some (MetaNum 0)) (hash empty) (none)))
(define false-val falsedummy)
(define (renew-false env sto)
  (if (or (VObjectClass? false-val)
          (and (is-obj-ptr? false-val sto)
               (VUndefined? (some-v (VObjectClass-class (fetch-ptr false-val sto))))))
      (local [(define with-class
                (VObjectClass 'bool (some (MetaNum 0)) (hash empty)
                              (some (fetch-once (some-v (lookup '%bool env)) sto))))
              (define new-false (alloc-result with-class sto))]
        (begin
          (set! false-val (v*s-v new-false))
          new-false))
      (v*s false-val sto)))

(define nonedummy (VObjectClass 'none (some (MetaNone)) (hash empty) (none)))
(define vnone nonedummy)
(define (renew-none env sto)
  (if (or (VObjectClass? vnone)
          (and (is-obj-ptr? vnone sto)
               (VUndefined? (some-v (VObjectClass-class (fetch-ptr vnone sto))))))
      (local [(define with-class
                (VObjectClass 'none (some (MetaNone)) (hash empty)
                              (some (fetch-once (some-v (lookup '%none env)) sto))))
              (define new-false (alloc-result with-class sto))]
        (begin
          (set! vnone (v*s-v new-false))
          new-false))
      (v*s vnone sto)))

(define (reset-state)
  (begin
    (set! true-val truedummy)
    (set! false-val falsedummy)
    (set! vnone nonedummy)))

(define (get-optionof-field [n : symbol] [c : CVal] [e : Env] [s : Store]) : (optionof CVal)
  (begin ;(display n) (display " -- ") (display c) (display "\n") (display e) (display "\n\n")
  (type-case CVal c
    [VObjectClass (antecedent mval d class) 
                    (let ([w (hash-ref (VObjectClass-dict c) n)])
              (type-case (optionof Address) w
                [some (w) (some (fetch w s))]
                [none () (let ([mayb-base (lookup antecedent e)])
                           (if (some? mayb-base)
                             (let ([base (fetch (some-v mayb-base) s)])
                                 (get-optionof-field n base e s))
                                           (none)))]))]
    [else (error 'interp "Not an object with functions.")])))


(define (make-set [vals : (listof CVal)]) : Set
  (foldl (lambda (elt st)
                 (set-add st elt))
         (set)
         vals))

;; any: any of a list of boolean (used in the c3 mro algorithm)
(define (any [bs : (listof boolean)]) : boolean
  (foldr (lambda (e1 e2) (or e1 e2)) #f bs))



;; syntactic sugars to avoid writing long expressions in the core language
(define (py-num [n : number])
  (CObject (gid '%num) (some (MetaNum n))))

(define (py-len name)
  (CApp (CGetField (CId name (LocalId)) '__len__)
        (list)
        (none)))

(define (py-getitem name index)
  (CApp (CGetField (CId name (LocalId)) '__getitem__)
        (list (CObject (gid '%num) (some (MetaNum index))))
        (none)))

(define-syntax pylam
  (syntax-rules ()
    [(_ (arg ...) body)
     (CFunc (list arg ...) (none) body (none))]))

(define-syntax pyapp
  (syntax-rules ()
    [(_ fun arg ...)
     (CApp fun (list arg ...) (none))]))

(define (Id x)
  (CId x (LocalId)))
(define (gid x)
  (CId x (GlobalId)))

(define (Let id val lastbody)
  (CLet id (LocalId) val lastbody))

(define-syntax (Prim stx)
  (syntax-case stx ()
    [(_ op arg ...) #'(CBuiltinPrim op (list arg ...))]))

(define-syntax (Method stx)
  (syntax-case stx ()
    [(_ obj name arg ...) #'(CApp (CGetField obj name) (list arg ...) (none))]))


 
(define (make-builtin-str [s : string]) : CExpr
  (CObject (gid '%str) (some (MetaStr s))))

(define (make-builtin-num [n : number]) : CExpr
  (CObject
    (if (exact? n)
        (gid '%int)
        (gid '%float))
    (some (MetaNum n))))

(define (Num num)
  (make-builtin-num num))

(define-syntax (Construct stx)
  (syntax-case stx ()
    [(_ class arg ...)
     #'(CApp (CGetField class '__init__) (list arg ...) (none))]))

(test (Let 'x (CNone) (make-builtin-str "foo"))
      (CLet 'x (LocalId) (CNone)
        (make-builtin-str "foo")))

(test (Prim 'num< (make-builtin-str "foo") (make-builtin-str "bar"))
      (CBuiltinPrim 'num< (list (make-builtin-str "foo") (make-builtin-str "bar"))))

;; strip the CLet in CModule
(define (get-module-body (es : CExpr)) : CExpr
  (type-case CExpr es
    [CModule (pre body) (get-module-body body)]
    [CLet (x type bind body)
          (get-module-body body)]   
    [else es]))

;; builtin-class: used construct builtin classes in the core language
(define (builtin-class [name : symbol] [bases : (listof symbol)] [body : CExpr]) : CExpr
  (CClass name
          ;; builtin classes are bound to ids in the global scope
          (CTuple (CNone) ;; we may not have a tuple class object yet
                  (map (lambda (id) (CId id (GlobalId))) bases))
          body))
