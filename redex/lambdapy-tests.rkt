#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This file contains reduction tests - terms and what they ;;
;; should reduce to (after any number of steps).            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex
         (only-in "../base/python-lib-bindings.rkt" lib-function-dummies lib-functions bind-left bind-right)
         "../base/python-lib.rkt"
         (only-in "../base/util.rkt" seq-ops)
         "../base/python-core-syntax.rkt"
         "../base/python-tools.rkt"
         "core-to-redex.rkt"
         "lambdapy-reduction.rkt"
         "lambdapy-core.rkt"
         "lambdapy-prim.rkt")

(require (only-in plai-typed/untyped some none))

(set-pypath "/home/joe/src/Python-3.2.3/python")

(define-syntax (expect stx)
  (syntax-case stx ()
      ((_ e v)
       #'(test-->>∃ λπ-red (term (e () ()))
                    (λ (p) (equal? (term v) (first p)))))))

(define-syntax (expect-raw stx)
  (syntax-case stx ()
      ((_ e pat)
       #'(test-->>∃ λπ-red (term (,e () ()))
                    (λ (p) (redex-match? λπ pat (first p)))))))


(define-syntax (full-expect stx)
  (syntax-case stx ()
      ((_ (e ε Σ) pat)
       #'(test-->>∃ λπ-red (term (e ε Σ))
                    (λ (p)
                      (if (not
                              (and
                                (redex-match? λπ pat p)))
                          (begin #;(display "Found:\n") #;(pretty-write p) #f)
                          #t))))))


;; Primitive values
(expect none vnone)
(expect true vtrue)
(expect false vfalse)
(expect undefined (undefined-val))

;; object values
(expect (list none (true false))
        (obj-val list (meta-list (vtrue vfalse)) () vnone))

;; control flow
(expect (if true none undefined) vnone)
(expect (if false none undefined) (undefined-val))
(expect (if (raise vtrue) false false)
	(err vtrue))
(expect (seq true false) vfalse)
(expect (seq (raise vtrue) false)
	(err vtrue))
(expect (seq false (raise vtrue))
	(err vtrue))
#;(expect (seq (return true) false)
	vtrue)
(expect (while true break false)
	break-r)


;; binding
(expect (let (x local = vtrue) in (id x local))
	vtrue)
(expect (let (x local = (raise vtrue)) in false)
	(err vtrue))
(expect (let (x local = vtrue) in (raise vfalse))
	(err vfalse))

;; prims
(expect (builtin-prim "is" (true true)) vtrue)
(expect (builtin-prim "is" (true false)) vfalse)
(expect (builtin-prim "is" ((mknum 1) (mknum 1))) vtrue)
(expect (builtin-prim "is" ((mknum 1) (mknum 2))) vfalse)
#| ; NOTE(dbp): currently the implementation of numeric primitives,
   ; which we have copied, is buggy, and as a result, these tests don't pass!
   ; see: https://groups.google.com/d/msg/lambda-py/szbm86ron8Q/PbFO7RKOpKMJ
   ; -- agree with you. i was not sure whether we could change core's semantics
   ; -- so i just did this... -yao
(expect (builtin-prim "num+" ((mknum 1) (mknum 1))) (make-num 2))
(expect (builtin-prim "num-" ((mknum 2) (mknum 1))) (make-num 1))
(expect (builtin-prim "num*" ((mknum 2) (mknum 3))) (make-num 6))
(expect (builtin-prim "num/" ((mknum 4) (mknum 2))) (make-num 2))
(expect (builtin-prim "num//" ((mknum 5) (mknum 2))) (make-num 2))
(expect (builtin-prim "num%" ((mknum 5) (mknum 2))) (make-num 1))
|#
(expect (builtin-prim "num=" ((mknum 1) (mknum 1))) vtrue)
(expect (builtin-prim "num=" ((mknum 1) (mknum 2))) vfalse)
(expect (builtin-prim "num>" ((mknum 1) (mknum 1))) vfalse)
(expect (builtin-prim "num>" ((mknum 2) (mknum 1))) vtrue)
(expect (builtin-prim "num>" ((mknum 1) (mknum 2))) vfalse)

(expect (builtin-prim "num<" ((mknum 1) (mknum 1))) vfalse)
(expect (builtin-prim "num<" ((mknum 2) (mknum 1))) vfalse)
(expect (builtin-prim "num<" ((mknum 1) (mknum 2))) vtrue)

(expect (builtin-prim "num<=" ((mknum 1) (mknum 1))) vtrue)
(expect (builtin-prim "num<=" ((mknum 2) (mknum 1))) vfalse)
(expect (builtin-prim "num<=" ((mknum 1) (mknum 2))) vtrue)

(expect (builtin-prim "num>=" ((mknum 1) (mknum 1))) vtrue)
(expect (builtin-prim "num>=" ((mknum 2) (mknum 1))) vtrue)
(expect (builtin-prim "num>=" ((mknum 1) (mknum 2))) vfalse)

(expect
  (builtin-prim "list-getitem" (
    (obj-val %list (meta-list ((pointer-val 0) (pointer-val 1))) ())
    (obj-val %int (meta-num 0) ())))
  (pointer-val 0))

(expect
  (builtin-prim "list-getitem" (
    (fetch (list vnone ((pointer-val 0) (pointer-val 1))))
    (fetch (object vnone (meta-num 0)))))
  (pointer-val 0))

(full-expect
 ((id str global) ((str 1)) ((1 (obj-val %str (meta-str "just-var-lookup") ()))))
 ((obj-val %str (meta-str "just-var-lookup") ())  ((str 1)) ((1 (obj-val %str (meta-str "just-var-lookup") ())))))

(full-expect
 ((get-field (object (id %str global) (meta-str "foo"))
             "inherited")
  {(%str 5)}
  {(4 (obj-val %type (meta-class %str) (("__mro__" 9) ("inherited" 6))))
   (5 (pointer-val 4))
   (6 (pointer-val 7))
   (7 (obj-val %str (meta-str "should be looked up") ()))
   (9 (pointer-val 10))
   (10 (obj-val %tuple (meta-tuple ((pointer-val 4))) ()))})
 ((pointer-val 7)
  ε Σ))

(full-expect
 ((get-field (object (id %str global) (meta-str "foo"))
             "shadowed")
  {(%str 5)}
  {(4 (obj-val type (meta-class %str) (("__mro__" 9) ("shadowed" 6))))
   (5 (pointer-val 4))
   (6 (pointer-val 7))
   (7 (obj-val %str (meta-str "should be looked up") ()))
   (8 (obj-val %object (no-meta) (("shadowed" 9))))
   (9 (pointer-val 10))
   (10 (obj-val %tuple (meta-tuple ((pointer-val 4) (pointer-val 8))) ()))})
 ((pointer-val 7)
  ε Σ))

(full-expect
 ((get-field (object (id %str global) (meta-str "foo"))
             "inherited")
  {(%str 5)}
  {(4 (obj-val type (meta-class %str) (("__mro__" 9) ("not-inherited" 6))))
   (5 (pointer-val 4))
   (6 (pointer-val 7))
   (7 (obj-val %str (meta-str "should not be looked up") ()))
   (8 (obj-val %object (no-meta) (("inherited" 9))))
   (9 (pointer-val 10))
   (10 (obj-val %tuple (meta-tuple ((pointer-val 4) (pointer-val 8))) ()))})
 ((pointer-val 10)
  ε Σ))

(define inherit-Σ (term {(4 (obj-val type (meta-class %str) (("__mro__" 9) ("not-inherited" 6))))
   (5 (pointer-val 4))
   (6 (pointer-val 7))
   (7 (obj-val %str (meta-str "should not be looked up") ()))
   (8 (obj-val %object (no-meta) (("inherited" 11))))
   (9 (pointer-val 10))
   (10 (obj-val %tuple (meta-tuple ((pointer-val 4) (pointer-val 8))) ()))
   (11 (pointer-val 12))
   (12 (obj-val %function (meta-closure (λ (self) (no-var) none (no-var))) ()))}))

(full-expect
 ((get-field (object (id %str global) (meta-str "foo"))
             "inherited")
  {(%str 5)}
  ,inherit-Σ)
 ((pointer-val ref_meth)
  ε ((ref val) ...
     (ref_meth (obj-val method (no-meta) (("__self__" ref_s) ("__func__" ref_f))))
     (ref_rest val_rest) ...)))


(full-expect
  ((object (id %str global) (meta-str "just-object-creation"))
   {(%str 1)}
   {(0 (obj-val %type (meta-class str) ()))
    (1 (pointer-val 0))})
  ((pointer-val ref_1)
   {(%str 1)}
   {(0 (obj-val %type (meta-class str) ()))
    (1 (pointer-val 0))
    (ref_1 (obj-val (pointer-val 0) (meta-str "just-object-creation") ()))}))


(expect-raw
  (core->redex (CObject (CSym 'foo) (some (MetaStr "bar"))))
  (pointer-val ref))

(full-expect
 (,(core->redex (CGetField (CObject (CId '%str (GlobalId)) (some (MetaStr "foo"))) 'inherited))
  {(%str 5)}
  ,inherit-Σ)
 ((pointer-val ref_meth)
  ε ((ref val) ... (ref_meth (obj-val any_cls (no-meta) (("__self__" ref_s) ("__func__" ref_f))))
      (ref_rest val_rest) ...)))

(expect-raw
 (core->redex (CSeq (CSym 'foo) (CSym 'bar)))
 (sym "bar"))

(full-expect
 (,(core->redex (CApp (CFunc '(x) (none) (CReturn (CId 'x (LocalId))) (none))
                      (list (CObject (CId '%str (GlobalId))
                                     (some (MetaStr "identity function"))))
                      (none)))
  {(%str 5)}
  ,inherit-Σ)
 ((pointer-val ref_str)
  ε
  {(ref val) ... (ref_str (obj-val (pointer-val ref_cls)
                                   (meta-str "identity function")
                                   ()))
   (ref_n val_n) ...}))

(full-expect
 (,(core->redex (CApp (CFunc '() (none) (CReturn (CObject (CId '%str (GlobalId))
                                                          (some (MetaStr "no args")))) (none))
                      (list)
                      (none)))
  {(%str 5)}
  ,inherit-Σ)
 ((pointer-val ref_str)
  ε
  {(ref val) ... (ref_str (obj-val (pointer-val ref_cls)
                                   (meta-str "no args")
                                   ()))
   (ref_n val_n) ...}))

(full-expect
 (,(core->redex (CApp
                 (CApp (CFunc '(x) (none)
                             (CReturn (CFunc '(y) (none) (CReturn (CId 'x (LocalId))) (none)))
                             (none))
                       (list (CObject (CId '%str (GlobalId))
                                      (some (MetaStr "close over this one"))))
                       (none))
                 (list (CNone))
                 (none)))
  {(%str 5)}
  ,inherit-Σ)
 ((pointer-val ref_str)
  ε
  {(ref val) ... (ref_str (obj-val (pointer-val ref_cls)
                                   (meta-str "close over this one")
                                   ()))
   (ref_n val_n) ...}))

(full-expect
 (,(core->redex (get-core-syntax (open-input-string "
def f(x):
  return x
f('a-str')
")))
  {(%str 1)}
  {(1 vnone)})
 ((pointer-val ref_str)
  {(%str 1) (f ref_f)}
  {(ref_1 val_1) ...
   (ref_str (obj-val any_cls (meta-str "a-str") ()))
   (ref_n val_n) ...}))

(full-expect
 (,(core->redex (get-core-syntax (open-input-file "../base/pylib/none.py")))
  () ())
 ((err val) ε Σ))

(full-expect
 (,(core->redex (CBuiltinPrim 'num+
                              (list 
                               (CObject (CNone) (some (MetaNum 4)))
                               (CObject (CNone) (some (MetaNum 5))))))
  () ())
 ((pointer-val ref)
  ε
  ((ref_1 val_1) ...
   (ref (obj-val any_cls (meta-num 9) ()))
   (ref_n val_n) ...)))

(full-expect
 (,(core->redex (CLet 'x (LocalId) (CObject (CNone) (some (MetaStr "foo")))
                      (CSeq
                       (CAssign (CGetField (CId 'x (LocalId)) 'updated) (CObject (CNone) (some (MetaStr "val"))))
                       (CGetField (CId 'x (LocalId)) 'updated))))
  () ())
 ((pointer-val ref)
  ε
  ((ref_1 val_1) ...
   (ref (obj-val any_cls (meta-str "val") ()))
   (ref_n val_n) ...)))

 

(full-expect
 (,(core->redex (cascade-lets lib-function-dummies (CTrue)))
  () ())
 ((obj-val %bool (meta-num 1) ()) ε Σ))



(full-expect
 (,(core->redex (cascade-lets lib-function-dummies
                              (seq-ops (append
                                        (map (lambda (b) (bind-right b)) (take lib-functions 4))
                                        (list (CTrue))
                                        ))))
  () ())
 ((obj-val %bool (meta-num 1) ()) ε Σ))

(test-results)
