#lang racket
(require "lambdapy-test-util.rkt")

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
 ((app (fun () (no-var)
            (return (builtin-prim "tuple-getitem" ((fetch (id args local)) (fetch (object vnone (meta-num 0))))))
            (no-var))
       ((object vnone (meta-str "get-this-one"))
        (object vnone (meta-str "not-this-one"))))
  () ())
 ((err (obj-val any_cls (meta-str "arity-mismatch") any_dict)) ε Σ))

(full-expect
 ((app (fun () (args)
            (return (builtin-prim "tuple-getitem" ((fetch (id args local)) (fetch (object vnone (meta-num 0))))))
            (no-var))
       ((object vnone (meta-str "get-this-one"))
        (object vnone (meta-str "not-this-one"))))
  () ())
 ((pointer-val ref_arg)
  ε
  ((ref_1 val_1) ...
   (ref_arg (obj-val any_cls (meta-str "get-this-one") any_dict))
   (ref_n val_n) ...)))
