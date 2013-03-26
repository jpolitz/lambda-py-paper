#lang racket

(require "lambdapy-test-util.rkt")
(full-expect
 (,(core->redex (get-core-syntax (open-input-string "
def f(x):
  return x
f('a-str')
")))
  {(%str 1) (%locals 2)}
  {(1 vnone)
   (2 vnone)})
 ((pointer-val ref_str)
  {(%str 1) (%locals 2) (f ref_f)}
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
  
#;(full-expect
   (,(core->redex (cascade-lets lib-function-dummies (CTrue)))
    () ())
   ((obj-val %bool (meta-num 1) ()) ε Σ))

#;(full-expect
 (,(core->redex (cascade-lets lib-function-dummies
                              (seq-ops (append
                                        (map (lambda (b) (bind-right b)) lib-functions)
                                        (list (CTrue))
                                        ))))
  () ())
 ((obj-val %bool (meta-num 1) ()) ε Σ))