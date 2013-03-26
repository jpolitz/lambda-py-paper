#lang racket

(require "lambdapy-test-util.rkt")


(full-expect
 ((app
   (fun (f) (no-var)
         (return (builtin-prim "str-getitem"
                               ((app (id f local) ())
                                (mknum 0))))
         (no-var))
   ((fun () (no-var)
          (seq
           (return ,(redex-strv "get-my-g"))
           (raise (sym "should not reach")))
          (no-var))))
  () ())
 ((obj-val any_cls (meta-str "g") any_dict) ε Σ))

(full-expect
 ((return (sym "top return")) () ())
 ((err (sym "toplevel-return")) () ()))