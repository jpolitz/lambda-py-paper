#lang racket

(require
  redex
  (only-in plai-typed/untyped some-v some?)
  "lambdapy-core.rkt"
  "../base/builtins/type.rkt" ;; for c3-merge, c3-select mro algorithm
  )

(provide (all-defined-out))

(define-term vnone (obj-val %none (meta-none) ()))
(define-term vtrue (obj-val %bool (meta-num 1) ()))
(define-term vfalse (obj-val %bool (meta-num 0) ()))

(define-metafunction λπ
  mknum : number -> val
  [(mknum number) (obj-val ,(if (exact? (term number)) (term int) (term float))
                           (meta-num number)
                           ())])

(define-metafunction λπ
  truthy? : val -> #t or #f
  [(truthy? (fun-val any ...)) #t]
  [(truthy? (obj-val x (meta-num number) (any ...))) ,(not (= 0 (term number)))]
  [(truthy? (obj-val x (meta-str string) (any ...))) ,(not (string=? "" (term string)))]
  [(truthy? (obj-val x (meta-list (val ...)) (any ...))) ,(not (empty? (term (val ...))))]
  [(truthy? (obj-val x (meta-tuple (val ...)) (any ...))) ,(not (empty? (term (val ...))))]
  [(truthy? (obj-val x (meta-dict ((val_1 val_2) ...)) (any ...))) ,(not (empty? (term (val_1 ...))))]
  [(truthy? (obj-val x (meta-set (val ...)) (any ...))) ,(not (empty? (term (val ...))))]
  [(truthy? (obj-val x (meta-none) (any ...))) #f]
  [(truthy? (obj-val x mval (any ...))) #t]
  [(truthy? (obj-val x (any ...))) #t]
  [(truthy? undefined-val) #f])

(define-metafunction λπ
  δ : op val ... ε Σ -> val
  [(δ "list-getitem" (obj-val any_c1 (meta-list (val_0 ... val_1 val_2 ...)) any_1) (obj-val any_c2 (meta-num number_2) any_2) ε Σ)
   val_1
   (side-condition (equal? (length (term (val_0 ...))) (term number_2)))]
  [(δ "list-getitem" (obj-val any_c1 (meta-list (val_1 ...)) any_1) (obj-val any_c2 (meta-num number_2) any_2) ε Σ)
   (obj-val %none (meta-none) ())]
  [(δ "list-setitem" (obj-val any_c1 (meta-list (val_0 ... val_1 val_2 ...)) any_1) (obj-val x_2 (meta-num number_2) any_2) val_3 val_4 ε Σ)
   (obj-val val_4 (meta-list (val_0 ... val_3 val_2 ...)) ())
   (side-condition (equal? (length (term (val_0 ...))) (term number_2)))]
  #;[(δ "list-getitem" (obj-val any_1 (meta-list (val_1 ...)) any_2) (obj-val any_3 (meta-num number_2) any_4) ε Σ)
   ,(if (and (exact? (term number_2)) (> (length (term (val_1 ...))) (term number_2)))
        (list-ref (term (val_1 ...)) (term number_2))
        (term vnone))]
  [(δ "num+" (obj-val any_cls (meta-num number_1) any_1) (obj-val any_cls2 (meta-num number_2) any_2) ε Σ)
   (obj-val any_cls (meta-num ,(+ (term number_1) (term number_2))) ())]
  [(δ "not" val ε Σ)
   ,(if (term (truthy? val)) (term vfalse) (term vtrue))]
  [(δ "print" val ε Σ)
   ,(begin (display (term val)) (display "\n") (term vnone))] ;; not sure how to do print for now
  #;[(δ "callable" (fun-val any ...) ε Σ)
   vtrue]
  [(δ "is-func?" (obj-val any_cls (meta-closure any_closure) any_dict) ε Σ)
   vtrue]
  [(δ "is-func?" val ε Σ) vfalse]
  [(δ "callable" (obj-val x (meta-class any) any) ε Σ)
   vtrue]
  [(δ "callable" val ε Σ)
   vfalse]
  [(δ "is" val_1 val_2 ε Σ)
   ,(if (eq? (term val_1) (term val_2)) (term vtrue) (term vfalse))] ;; current interp does this
  [(δ "isnot" val_1 val_2 ε Σ)
   ,(if (eq? (term val_1) (term val_2)) (term vfalse) (term vtrue))]
  [(δ "isinstance" val_1 (obj-val x (meta-class x_class) any) ε Σ)
   ,(if (term (object-is? val_1 x_class ε Σ)) (term vtrue) (term vfalse))]
  ;; numbers, no type-checking yet
  [(δ "num-" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   ,(make-num (- (term number_1) (term number_2)))]
  [(δ "num*" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   (obj-val num (meta-num ,(* (term number_1) (term number_2))) ())]
  [(δ "num*" (name v1 (obj-val x_1 (meta-num number_1) any_1)) (name v2 (obj-val x_2 (meta-str string_2) any_2)) ε Σ)
   (δ "str*" v2 v1 ε Σ)]
  [(δ "num/" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   (obj-val num (meta-num ,(/ (term number_1) (term number_2))) ())]
  [(δ "num//" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   (obj-val num (meta-num ,(quotient (term number_1) (term number_2))) ())]
  [(δ "num%" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   (obj-val num (meta-num ,(remainder (term number_1) (term number_2))) ())]
  [(δ "num=" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   ,(if (= (term number_1) (term number_2)) (term vtrue) (term vfalse))]
  [(δ "num>" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   ,(if (> (term number_1) (term number_2)) (term vtrue) (term vfalse))]
  [(δ "num<" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   ,(if (< (term number_1) (term number_2)) (term vtrue) (term vfalse))]
  [(δ "num>=" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   ,(if (>= (term number_1) (term number_2)) (term vtrue) (term vfalse))]
  [(δ "num<=" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   ,(if (<= (term number_1) (term number_2)) (term vtrue) (term vfalse))]
  [(δ "numcmp" (obj-val x_1 (meta-num number_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   ,(cond
      [(< (term number_1) (term number_2)) (term (obj-val num (meta-num -1) ()))]
      [(> (term number_1) (term number_2)) (term (obj-val num (meta-num 1) ()))]
      [else (term (obj-val num (meta-num 0) ()))])]
  [(δ "num-str" (obj-val x (meta-num number) any) ε Σ)
   (obj-val str (meta-str ,(number->string (term number))) ())]
  ;; strings, no type-checking yet
  [(δ "str+" (obj-val x_1 (meta-str string_1) any_1) (obj-val x_2 (meta-str string_2) any_2) ε Σ)
   (obj-val str (meta-str ,(string-append (term string_1) (term string_2))) ())]
  [(δ "str=" (obj-val x_1 (meta-str string_1) any_1) (obj-val x_2 (meta-str string_2) any_2) ε Σ)
   ,(if (string=? (term string_1) (term string_2)) (term vtrue) (term vfalse))]
  [(δ "str*" (obj-val x_1 (meta-str string_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   (obj-val str (meta-str ,(string-append* (build-list (term number_2) (lambda (n) (term string_1))))) ())]
  [(δ "strcmp" (obj-val x_1 (meta-str string_1) any_1) (obj-val x_2 (meta-str string_2) any_2) ε Σ)
   ,(cond
      [(string<? (term string_1) (term string_2)) (term (obj-val num (meta-num -1) ()))]
      [(string>? (term string_1) (term string_2)) (term (obj-val num (meta-num 1) ()))]
      [else (term (obj-val num (meta-num 0) ()))])]
  [(δ "strlen" (obj-val x (meta-str string) any) ε Σ)
   (obj-val num (meta-num ,(string-length (term string))) ())]
  [(δ "strbool" (obj-val x (meta-str string) any) ε Σ)
   ,(if (string=? (term string) "") (term vfalse) (term vtrue))]
  [(δ "strmin" (obj-val x (meta-str string) any) ε Σ)
   (obj-val str (meta-str string_new) ())
   (where string_new ,(make-string 1
                                   (integer->char
                                    (foldl (lambda (c res)
                                             (min res c))
                                           ;; the maximum char integer is currently #x10FFFF
                                           ;; should find a better way to do this
                                           #x110000
                                           (map char->integer
                                                (string->list (term string)))))))]
  [(δ "strmax" (obj-val x (meta-str string) any) ε Σ)
   (obj-val str (meta-str string_new) ())
   (where string_new ,(make-string 1
                                   (integer->char
                                    (foldl (lambda (c res)
                                             (max res c))
                                           -1
                                           (map char->integer
                                                (string->list (term string)))))))]
  [(δ "strin" (obj-val x_1 (meta-str string_1) any_1) (obj-val x_2 (meta-str string_2) any_2) ε Σ)
   ,(if (or (< (string-length (string-replace (term string_1) (term string_2) ""))
               (string-length (term string_1)))
            (string=? (term string_2) ""))
        (term vtrue)
        (term vfalse))]
  [(δ "str-getitem" (obj-val x_1 (meta-str string_1) any_1) (obj-val x_2 (meta-num number_2) any_2) ε Σ)
   (obj-val str (meta-str string_new) ())
   (where string_new ,(make-string 1 (string-ref (term string_1) (term number_2))))]
  ;; rename it from strlist to str-list for consistency
  [(δ "str-list" (obj-val x (meta-str string) any) ε Σ)
   (obj-val list (meta-list ,(map (lambda (s) (term (obj-val str (meta-str ,(make-string 1 s)) ())))
                                   (string->list (term string))))
            ())]
  [(δ "str-tuple" (obj-val x (meta-str string) any) ε Σ)
   (obj-val tuple (meta-tuple ,(map (lambda (s) (term (obj-val str (meta-str ,(make-string 1 s)) ())))
                                   (string->list (term string))))
            ())]
  ;; bool
  [(δ "bool-init" (obj-val x (meta-tuple ()) any) ε Σ)
   vfalse]
  [(δ "bool-init" (obj-val x (meta-tuple (val_1 val ...)) any) ε Σ)
   ,(if (term (truthy? val_1)) (term vtrue) (term vfalse))]
  ;; list
  [(δ "list+" (obj-val x_1 (meta-list (val_1 ...)) any_1) (obj-val x_2 (meta-list (val_2 ...)) any_2) ε Σ)
   (obj-val list (meta-list (val_1 ... val_2 ...)) ())]
  [(δ "list-len" (obj-val x (meta-list (val ...)) any) ε Σ)
   (obj-val int (meta-num ,(length (term (val ...)))) ())]
  [(δ "list-in" (obj-val x_1 (meta-list (val_1 val ...)) any_1) val_2 ε Σ)
   vtrue
   (side-condition (equal? (term val_1) (term val_2)))] ;; interp uses equal?, but is it the correct thing?
  [(δ "list-in" (obj-val x_1 (meta-list (val_1 val ...)) any_1) val_2 ε Σ)
   (δ "list-in" (obj-val x_1 (meta-list (val ...)) any_1) val_2 ε Σ)]
  [(δ "list-in" (obj-val x_1 (meta-list ()) any_1) val_2 ε Σ)
   vfalse]
  [(δ "list-setitem" (obj-val x_1 (meta-list (val_1 ...)) any_1) (obj-val x_2 (meta-num number_2) any_2) val_3 ε Σ)
   (obj-val list (meta-list ,(list-replace (term number_2) (term val_3) (term (val_1 ...)))) ())]
  [(δ "type-new" (obj-val any_cls (meta-str string) any_dict) ε Σ)
   (obj-val %type (meta-class ,(string->symbol (term string))) ())]
  [(δ "type-uniqbases" (obj-val any_cls (meta-tuple ((pointer-val ref) ...)) any_dict) ε Σ)
   vtrue
   (side-condition (= (length (term (ref ...)))
                      (length (remove-duplicates (term (ref ...))))))]
  [(δ "type-uniqbases" val ε Σ)
   vfalse]

  [(δ "type-buildmro" 
    (obj-val any_cls1 (meta-tuple (val_1 ...)) any_dict1)  
    (obj-val any_cls2 (meta-tuple (val_2 ...)) any_dict2)  
    ε Σ)
   (type-buildmro-help (val_1 ...) (val_2 ...) Σ)])

;; NOTE(joe): We restrict store-lookup to returning values;
;; the special case for ref_unbound notices when an undefined
;; is matched in the store, and won't let it be looked up.
(define-metafunction λπ
  store-lookup : Σ ref -> val
  [(store-lookup ((ref_1 v+undef_1) ... (ref val) (ref_n v+undef_n) ...) ref)
   val])

(define-judgment-form λπ
  #:mode (store-lookup/j I I O)
  #:contract (store-lookup/j Σ ref val)
  [(store-lookup/j
    ((ref_1 v+undef_1) ... (ref val) (ref_n v+undef_n) ...) ref val)])

(define-metafunction λπ
  fetch-pointer : val Σ -> val
  [(fetch-pointer (pointer-val ref) Σ) (store-lookup Σ ref)])

(define-metafunction λπ
  get-mro : val Σ -> (val ...)
  [(get-mro (pointer-val ref_obj) Σ)
   (val_cls ...)
   (where (obj-val any_cls any_meta
                   ((string_1 ref_1) ...
                    ("__mro__" ref_mro)
                    (string_n ref_n) ...))
          (store-lookup Σ ref_obj))
   (where (obj-val any_cls2 (meta-tuple (val_cls ...)) any_dict)
          (fetch-pointer (store-lookup Σ ref_mro) Σ))])

(define-metafunction λπ
  get-base-mros : (val ...) Σ -> ((val ...) ...)
  [(get-base-mros () Σ) ()]
  [(get-base-mros (val val_rest ...) Σ)
   ((get-mro val Σ) val_restmros ...)
   (where (val_restmros ...)
          (get-base-mros (val_rest ...) Σ))])

(define (merge l1 l2)
  (define result (c3-merge l1 l2))
  (cond
    [(some? result) (some-v result)]
    [else '()])) ;; TODO(joe): failure case here

(define-metafunction λπ
  type-buildmro-help : (val ...) (val ...) Σ -> val
  [(type-buildmro-help (val_1 ...) (val_2 ...) Σ)
   (obj-val %tuple (meta-tuple (val_1 ... val_cls ...)) ())
   (where (val_cls ...)
          ,(merge (term (get-base-mros (val_2 ...) Σ)) (term (val_2 ...))))])

(define-metafunction λπ
  object-is? : val x ε Σ -> #t or #f
  [(object-is? (obj-val no-super any ...) x ε Σ) #f]
  [(object-is? (obj-val x any ...) x ε Σ) #t]
  [(object-is? (obj-val x any ...)
               x_class
               (name env (((x_1 ref_x1) ...) ... ((x_2 ref_x2) ... (x ref) (x_3 ref_x3) ...) ε ...))
               (name store ((ref_4 val_4) ... (ref val) (ref_5 val_5) ...)))
   (object-is? val x_class env store)
   (side-condition (not (member (term x) (append* (term ((x_1 ...) ...))))))
   (side-condition (not (member (term x) (term (x_2 ... x_3 ...)))))
   (side-condition (not (member (term ref) (term (ref_4 ... ref_5 ...)))))])

(define (make-num n)
  (term (obj-val ,(if (exact? n) (term int) (term float))
                 (meta-num ,n)
                 ())))

(define (list-replace i val l)
  (cond
    [(empty? l) (error 'util "list-replace out of range")] ;; TODO: should not raise error here
    [(= 0 i) (cons val (rest l))]
    [else (cons (first l) (list-replace (- i 1) val (rest l)))]))
