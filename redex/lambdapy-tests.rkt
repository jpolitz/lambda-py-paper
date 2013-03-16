#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This file contains reduction tests - terms and what they ;;
;; should reduce to (after any number of steps).            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex
         "lambdapy-reduction.rkt"
         "lambdapy-core.rkt"
         "lambdapy-prim.rkt")


(define-syntax (expect stx)
  (syntax-case stx ()
      ((_ e v)
       #'(test-->>∃ λπ-red (term (e (()) ()))
                    (λ (p) (equal? (term v) (first p)))))))

(define-syntax (full-expect stx)
  (syntax-case stx ()
      ((_ (e εs Σ) pat)
       #'(test-->>∃ λπ-red (term (e εs Σ))
                    (λ (p)
                      (if (not
                              (and
                                (redex-match? λπ pat p)))
                          (begin (display "Found:\n") (pretty-write p) #f)
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
(expect (if (exception-r vtrue) false false)
	(exception-r vtrue))
(expect (seq true false) vfalse)
(expect (seq (raise vtrue) false)
	(exception-r vtrue))
(expect (seq false (raise vtrue))
	(exception-r vtrue))
(expect (seq (return true) false)
	(return-r vtrue))
(expect (while true break false)
	break-r)


;; binding
(expect (let (x local vtrue) (id x local))
	vtrue)
(expect (let (x local (exception-r vtrue)) false)
	(exception-r vtrue))
(expect (let (x local vtrue) (exception-r vfalse))
	(exception-r vfalse))

;; prims
(expect (prim2 "is" true true) vtrue)
(expect (prim2 "is" true false) vfalse)
(expect (prim2 "is" (mknum 1) (mknum 1)) vtrue)
(expect (prim2 "is" (mknum 1) (mknum 2)) vfalse)
#| ; NOTE(dbp): currently the implementation of numeric primitives,
   ; which we have copied, is buggy, and as a result, these tests don't pass!
   ; see: https://groups.google.com/d/msg/lambda-py/szbm86ron8Q/PbFO7RKOpKMJ
   ; -- agree with you. i was not sure whether we could change core's semantics
   ; -- so i just did this... -yao
(expect (prim2 "num+" (mknum 1) (mknum 1)) (make-num 2))
(expect (prim2 "num-" (mknum 2) (mknum 1)) (make-num 1))
(expect (prim2 "num*" (mknum 2) (mknum 3)) (make-num 6))
(expect (prim2 "num/" (mknum 4) (mknum 2)) (make-num 2))
(expect (prim2 "num//" (mknum 5) (mknum 2)) (make-num 2))
(expect (prim2 "num%" (mknum 5) (mknum 2)) (make-num 1))
|#
(expect (prim2 "num=" (mknum 1) (mknum 1)) vtrue)
(expect (prim2 "num=" (mknum 1) (mknum 2)) vfalse)
(expect (prim2 "num>" (mknum 1) (mknum 1)) vfalse)
(expect (prim2 "num>" (mknum 2) (mknum 1)) vtrue)
(expect (prim2 "num>" (mknum 1) (mknum 2)) vfalse)

(expect (prim2 "num<" (mknum 1) (mknum 1)) vfalse)
(expect (prim2 "num<" (mknum 2) (mknum 1)) vfalse)
(expect (prim2 "num<" (mknum 1) (mknum 2)) vtrue)

(expect (prim2 "num<=" (mknum 1) (mknum 1)) vtrue)
(expect (prim2 "num<=" (mknum 2) (mknum 1)) vfalse)
(expect (prim2 "num<=" (mknum 1) (mknum 2)) vtrue)

(expect (prim2 "num>=" (mknum 1) (mknum 1)) vtrue)
(expect (prim2 "num>=" (mknum 2) (mknum 1)) vtrue)
(expect (prim2 "num>=" (mknum 1) (mknum 2)) vfalse)

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
 ((get-field (fetch (object (id str local) (meta-str "foo")))
             "inherited")
  [{(str 5)}]
  {(4 (obj-val type (meta-class str) (("__mro__" 9) ("inherited" 6))))
   (5 (pointer-val 4))
   (6 (pointer-val 7))
   (7 (obj-val str (meta-str "should be looked up") ()))
   (9 (pointer-val 10))
   (10 (obj-val tuple (meta-tuple ((pointer-val 4))) ()))})
 ((pointer-val 7)
  εs Σ))

(full-expect
 ((get-field (fetch (object (id str local) (meta-str "foo")))
             "shadowed")
  [{(str 5)}]
  {(4 (obj-val type (meta-class str) (("__mro__" 9) ("shadowed" 6))))
   (5 (pointer-val 4))
   (6 (pointer-val 7))
   (7 (obj-val str (meta-str "should be looked up") ()))
   (8 (obj-val object (no-meta) (("shadowed" 9))))
   (9 (pointer-val 10))
   (10 (obj-val tuple (meta-tuple ((pointer-val 4) (pointer-val 8))) ()))})
 ((pointer-val 7)
  εs Σ))

(full-expect
 ((get-field (fetch (object (id str local) (meta-str "foo")))
             "inherited")
  [{(str 5)}]
  {(4 (obj-val type (meta-class str) (("__mro__" 9) ("not-inherited" 6))))
   (5 (pointer-val 4))
   (6 (pointer-val 7))
   (7 (obj-val str (meta-str "should be looked up") ()))
   (8 (obj-val object (no-meta) (("inherited" 9))))
   (9 (pointer-val 10))
   (10 (obj-val tuple (meta-tuple ((pointer-val 4) (pointer-val 8))) ()))})
 ((pointer-val 10)
  εs Σ))

(full-expect
  ((object (id str local) (meta-str "foo"))
   [{(str 1)}]
   {(0 (obj-val type (meta-class str) ()))
    (1 (pointer-val 0))})
  ((pointer-val ref_1)
   [{(str 1)}]
   {(0 (obj-val type (meta-class str) ()))
    (1 (pointer-val 0))
    (ref_1 (obj-val (pointer-val 0) (meta-str "foo") ()))}))



(test-results)
