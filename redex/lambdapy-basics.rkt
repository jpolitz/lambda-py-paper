#lang racket

(require "lambdapy-test-util.rkt")


;; Primitive values
(expect none vnone)
(expect true vtrue)
(expect false vfalse)

;; object values
(full-expect
 ((list none (true false)) () ())
 ((pointer-val 1)
  ()
  ((1 (obj-val val_none (meta-list (val_true val_false)) ())))))

;; control flow
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
        vnone)


;; binding
(expect (let (x local = vtrue) in (id x local))
        vtrue)
(expect (let (x local = (raise vtrue)) in false)
        (err vtrue))
(expect (let (x local = vtrue) in (raise vfalse))
        (err vfalse))

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
