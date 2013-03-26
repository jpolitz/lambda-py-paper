#lang racket

(require
  redex
  "lambdapy-core.rkt"
  "lambdapy-prim.rkt")

(provide λπ-red override-store class-lookup class-lookup-mro store-lookup maybe-bind-method subst)


(define λπ-red
  (reduction-relation
   λπ
   #:domain p
   (==> none vnone "none")
   (==> undefined (undefined-val) "undefined")
   (==> true vtrue "true")
   (==> false vfalse "false")
   (--> ((in-hole E (tryexcept (in-hole T (raise val)) x e_c e_e)) ε Σ)
        ((in-hole E (subst-one x ref e_c)) ε Σ_1)
        (where (Σ_1 ref) (extend-store Σ val)) ;;TODO(joe): else semantics
        "E-Catch")
   (--> ((in-hole E (list val_c (val ...))) ε Σ)
        ((in-hole E (pointer-val ref_new)) ε Σ_1)
        "E-List"
        (where (Σ_1 ref_new) (extend-store Σ (obj-val val_c (meta-list (val ...)) ()))))
   (--> ((in-hole E (tuple val_c (val ...))) ε Σ)
        ((in-hole E (pointer-val ref_new)) ε Σ_1)
        "E-Tuple"
        (where (Σ_1 ref_new) (extend-store Σ (obj-val val_c (meta-tuple (val ...)) ()))))
   (--> ((in-hole E (set val_c (val ...))) ε Σ)
        ((in-hole E (pointer-val ref_new)) ε Σ_1)
        "E-Set"
        (where (Σ_1 ref_new) (extend-store Σ (obj-val val_c (meta-set (val ...)) ()))))
   (--> ((in-hole E (fetch (pointer-val ref))) ε Σ)
        ((in-hole E (store-lookup Σ ref)) ε Σ)
        "E-Fetch")
   #;(--> ((in-hole E (fetch (obj-val any_cls any_meta any_dict))) ε Σ)
        ((in-hole E (raise (obj-val %str (meta-str "Fetch on object") ()))) ε Σ)
        "E-FetchErr")
   (--> ((in-hole E (set! (pointer-val ref) val)) ε Σ)
        ((in-hole E val) ε Σ_1)
        "E-Set!"
        (where Σ_1 (override-store Σ ref val)))
   (--> ((in-hole E (alloc val)) ε Σ)
        ((in-hole E (pointer-val ref_new)) ε Σ_1)
        "E-Alloc"
        (where (Σ_1 ref_new) (extend-store Σ val)))
   (--> ((in-hole E (fun (x ...) opt-var_1 e opt-var_2)) ε Σ)
        ((in-hole E (pointer-val ref_fun)) ε Σ_1)
        (where (Σ_1 ref_fun)
          (extend-store Σ (obj-val %function (meta-closure (λ (x ...) opt-var_1 e opt-var_2)) ())))
        "E-Fun")
   (--> ((in-hole E (object val mval)) ε Σ)
        ((in-hole E (pointer-val ref_new)) ε Σ_1)
        (where (Σ_1 ref_new) (extend-store Σ (obj-val val mval ())))
        "E-Object")
   (--> ((in-hole E (builtin-prim op (val ...))) ε Σ)
        ((in-hole E (δ op val ... ε Σ)) ε Σ)
        "builtin-prim")
   (--> ((in-hole E (if val e_1 e_2)) ε Σ)
        ((in-hole E e_1) ε Σ)
        (side-condition (term (truthy? val Σ)))
        "if-true")
   (--> ((in-hole E (if val e_1 e_2)) ε Σ)
        ((in-hole E e_2) ε Σ)
        (side-condition (not (term (truthy? val Σ))))
        "if-false")
   (==> (seq val e) e "E-Seq")
   ;; NOTE(yao): this may be unnecessary, since context T deals with it
   ;; I wrote it and then deleted.
   ;; same thing for "seq-return" etc., if we use context to do it
   #|
   (==> (if (exception-r val) e_1 e_2)
	(exception-r val)
	"if-exception")|#
   #|
   (==> (seq break-r e)
	break-r
	"seq-break")
   (==> (seq (exception-r val) e)
	(exception-r val)
	"seq-exception")|#
   (==> (while e_1 e_2 e_3)
        (if e_1 (loop e_2 (while e_1 e_2 e_3)) e_3)
        "E-While")
   (==> (loop val e) e "E-LoopNext")
   (==> (loop (in-hole H continue) e) e "E-LoopContinue")
   (==> (loop (in-hole H break) e) vnone "E-LoopBreak")

   (==> (frame (in-hole R (return val))) val "E-Return")
   (==> (frame val) val "E-FramePop")
   (--> ((in-hole R (return e)) ε Σ) ((err (sym "ill-formed-return")) ε Σ)
        "E-ReturnBad")

   (==> (tryfinally (in-hole R (return val)) e) (seq e (return val))
        "E-FinallyReturn")
   (==> (tryfinally (in-hole T (raise val)) e) (seq e (raise val))
        "E-FinallyRaise")
   (==> (tryfinally (in-hole H break) e) (seq e break)
        "E-FinallyBreak")
   (==> (tryfinally (in-hole H continue) e) (seq e continue)
        "E-FinallyContinue")

   (==> (tryexcept val x e_catch e_else)
        e_else
        "Try-Done")
   (==> (tryexcept (in-hole T (raise val)) x e_catch e_else)
        (let (x local = val) in e_catch)
        "Try-Catch")
   (==> (try (in-hole T (raise val)) ((except () e) e_exc ...) e_else e_finally)
        (try e () vnone e_finally)
        "try-exc-notype")
   (==> (try (in-hole T (raise val)) ((except () (x) e) e_exc ...) e_else e_finally)
        (try (let (x local = val) in e) () vnone e_finally)
        "try-exc-notype-named")
   (==> (try (in-hole T (raise val)) ((except (e_type1 e_type ...) e) e_exc ...) e_else e_finally)
        (try (if (builtin-prim "isinstance" (val e_type1)) ;; in principle "isinstance" should handle tuple (tuple (e_type1 e_type ...))
                 e
                 (try (in-hole T (exception-r val)) (e_exc ...) e_else vnone))
             () vnone e_finally)
        "try-exc-type")
   (==> (try (in-hole T (raise val)) ((except (e_type1 e_type ...) (x) e) e_exc ...) e_else e_finally)
        (try (if (builtin-prim "isinstance" (val e_type1)) ;; in principle "isinstance" should handle tuple (tuple (e_type1 e_type ...))
                 (let (x local = val) in e)
                 (try (in-hole T (raise val)) (e_exc ...) e_else vnone))
             () vnone e_finally)
        "try-exc-type-named")
   (==> (try (in-hole T r) (e_exc ...) e_else e_finally)
        (seq e_finally r)
        (side-condition (not (val? (term r))))
        (side-condition (not (redex-match? λπ (raise any) (term r))))
        "try-nonval")
   ;; NOTE(dbp): I don't think this is the correct behavior - uncaught exceptions
   ;; should percolate up as (exception-r val) results, NOT cause racket errors.
   ;;    agreed. (exception-r val) should be the reduction result. -yao
   (--> ((in-hole T (raise val)) ε Σ)
        ((err val) ε Σ)
        "exc-uncaught")
   (==> (module val e)
        e
        "module")
   #|
   (--> ((in-hole E (let (x_1 val) e))
         (ε_1 ε ...)
         Σ)
        ((in-hole E (subst (x_1) (x_new) e))
         ((extend-env ε_1 x_new ref_new) ε ...)
         (override-store Σ ref_new val))
        (fresh x_new)
        (where ref_new ,(new-loc))
        "let")|#
   (--> ((in-hole E (let (x global = v+undef) in e)) ε Σ)
        ((in-hole E e) (extend-env ε x ref) Σ_1)
        (where (Σ_1 ref) (extend-store Σ v+undef))
        "E-LetGlobal")
   (--> ((in-hole E (let (x local = v+undef) in e)) ε Σ)
        ((in-hole E (subst-one x ref e)) ε Σ_1)
        (where (Σ_1 ref) (extend-store Σ v+undef))
        "E-LetLocal")
   #|
   (==> (let (x_1 (exception-r val)) e_1)
        (exception-r val)
        "let-exc")|#
   (--> ((in-hole E (id x global))
         (name ε ((x_1 ref_1) ... (x ref) (x_2 ref_2) ...)) Σ)
        ((in-hole E (store-lookup Σ ref)) ε Σ)
        "E-GetGlobal")
   (--> ((in-hole E (id x local)) ε Σ)
        ((in-hole E (raise (obj-val %str (meta-str "Unbound identifier") ()))) ε Σ)
        "E-UnboundId")
   (--> ((in-hole E (id x global)) (name ε ((y ref) ...)) Σ)
        ((in-hole E (raise (obj-val %str (meta-str "Unbound global") ()))) ε Σ)
        "E-UnboundGlobal"
        (side-condition (not (member (term x) (term (y ...))))))
   (--> ((in-hole E (get-attr (pointer-val ref) (pointer-val ref_str))) ε Σ)
        ((in-hole E (store-lookup Σ ref_1)) ε Σ)
        (where (obj-val any_cls1 (meta-str string_1) any_dict) (store-lookup Σ ref_str))
        (where (obj-val any_cls2 mval ((string_2 ref_2) ... (string_1 ref_1) (string_3 ref_3) ...)) (store-lookup Σ ref))
        "E-GetField")
   (--> ((in-hole E (get-attr (pointer-val ref_obj) (pointer-val ref_str))) ε Σ)
        ((in-hole E val_result) ε Σ_result)
        (where (obj-val any_cls (meta-str string) any_dict) (store-lookup Σ ref_str))
        (where (obj-val (pointer-val ref) mval ((string_1 ref_2) ...))
               (store-lookup Σ ref_obj))
        (where (Σ_result val_result)
          (class-lookup (pointer-val ref_obj) (store-lookup Σ ref) string Σ))
        (side-condition (not (member (term string) (term (string_1 ...)))))
        "E-GetField-Class")
   (--> ((in-hole E (get-attr (pointer-val ref_obj) (pointer-val ref_str))) ε Σ)
        ((in-hole E val_result) ε Σ_result)
        (where (obj-val any_cls (meta-str string) any_dict) (store-lookup Σ ref_str))
        (where (obj-val x_cls mval ((string_1 ref_2) ...))
               (store-lookup Σ ref_obj))
        (where (Σ_result val_result)
          (class-lookup (pointer-val ref_obj) (store-lookup Σ (env-lookup ε x_cls)) string Σ))
        (side-condition (not (member (term string) (term (string_1 ...)))))
        "E-GetAttr-Class/Lazy")
   (--> ((in-hole E (assign (id x global) := val)) (name ε ((x_2 ref_2) ... (x ref) (x_3 ref_3) ...)) Σ)
        ((in-hole E val) ε (override-store Σ ref val))
        "E-AssignGlobal")
   (--> ((in-hole E (assign (id x global) := val)) (name ε ((y ref) ...)) Σ)
        ((in-hole E (raise (obj-val %str (meta-str "Unbound global") ()))) ε Σ)
        "E-AssignGlobalUnbound"
        (side-condition (not (member (term x) (term (y ...))))))
   (--> ((in-hole E (assign ref := val)) ε Σ)
        ((in-hole E val) ε (override-store Σ ref val))
        "E-AssignLocal")
   (--> ((in-hole E (set-attr (pointer-val ref_obj) (pointer-val ref_str) := val_1)) ε Σ)
        ((in-hole E val_1) ε (override-store Σ ref_1 val_1))
        (where (obj-val any_cls1 mval ((string_2 ref_2) ... (string_1 ref_1) (string_3 ref_3) ...))
               (store-lookup Σ ref_obj))
        (where (obj-val any_cls2 (meta-str string_1) any_dict) (store-lookup Σ ref_str))
        "E-AssignUpdate")
   (--> ((in-hole E (set-attr (pointer-val ref_obj) (pointer-val ref_str) := val_1)) ε Σ)
        ((in-hole E val_1) ε Σ_2)
        (where (obj-val any_cls1 mval ((string ref) ... )) (store-lookup Σ ref_obj))
        (where (Σ_1 ref_new) (extend-store Σ val_1))
        (where (obj-val any_cls2 (meta-str string_1) any_dict) (store-lookup Σ ref_str))
        (where Σ_2 (override-store Σ_1 ref_obj (obj-val any_cls1 mval ((string_1 ref_new) (string ref) ...))))
        (side-condition (not (member (term string_1) (term (string ...)))))
        "E-AssignAdd")
   (--> ((in-hole E (app (pointer-val ref_fun) (val ..._1))) ε Σ)
        ((in-hole E (frame (subst (x ...) (ref_arg ...) e))) ε Σ_1)
        (where (obj-val any_c (meta-closure (λ (x ..._1) (no-var) e opt-var)) any_dict)
               (store-lookup Σ ref_fun))
        (where (Σ_1 (ref_arg ...))
               (extend-store/list Σ (val ...)))
        "E-App")
   (--> ((in-hole E ref) ε (name Σ ((ref_1 v+undef_1) ... (ref val) (ref_n v+undef_n) ...)))
        ((in-hole E val) ε Σ)
        "E-GetVar")
   (--> ((in-hole E ref) ε (name Σ ((ref_1 v+undef_1) ... (ref (undefined-val)) (ref_n v+undef_n) ...)))
        ((in-hole E (raise (obj-val %str (meta-str "Uninitialized local") ()))) ε Σ)
        "E-GetVarUndef")
   with
   [(--> (in-hole P e_1) (in-hole P e_2))
    (==> e_1 e_2)]
   ))


(define-metafunction λπ
  extend-env : ε x ref -> ε
  [(extend-env ((x_2 ref_2) ...) x_1 ref_1) ((x_2 ref_2) ... (x_1 ref_1))])

(define-metafunction λπ
  env-lookup : ε x -> ref
  [(env-lookup ((x_1 ref_1) ... (x ref) (x_n ref_n) ...) x) ref])

(define-metafunction λπ
  override-store : Σ ref val -> Σ
  [(override-store ((ref_2 v+undef_2) ...) ref_1 val_1)
   ((ref_2 v+undef_2) ... (ref_1 val_1))
   (side-condition (not (member (term ref_1) (term (ref_2 ...)))))]
  [(override-store ((ref_2 v+undef_2) ... (ref_1 v+undef_0) (ref_3 v+undef_3) ...) ref_1 val_1)
   ((ref_2 v+undef_2) ... (ref_1 val_1) (ref_3 v+undef_3) ...)
   (side-condition (not (member (term ref_1) (term (ref_2 ...)))))])
 
(define-metafunction λπ
  extend-store : Σ v+undef -> (Σ ref)
  [(extend-store (name Σ ((ref v+undef) ...)) v+undef_new)
   (((ref v+undef) ... (ref_new v+undef_new)) ref_new)
   (where ref_new (get-new-loc Σ))])

(define-metafunction λπ
  extend-store/list : Σ (v+undef ...) -> (Σ (ref ...))
  [(extend-store/list Σ ()) (Σ ())]
  [(extend-store/list Σ (v+undef)) (Σ_1 (ref))
   (where (Σ_1 ref) (extend-store Σ v+undef))]
  [(extend-store/list Σ (v+undef v+undef_rest ...)) (Σ_2 (ref ref_rest ...))
   (where (Σ_1 ref) (extend-store Σ v+undef))
   (where (Σ_2 (ref_rest ...))
          (extend-store/list Σ_1 (v+undef_rest ...)))])

(define-metafunction λπ
  get-new-loc : Σ -> ref
  [(get-new-loc ((ref_1 v+undef_1) ...))
   ,(add1 (apply max (cons 0 (term (ref_1 ...)))))])

(define-metafunction λπ
  class-lookup-mro : (val ...) string Σ -> val
  [(class-lookup-mro ((pointer-val ref_c) val_rest ...) string Σ)
   (store-lookup Σ ref)
   (where (obj-val any_1 any_2 ((string_1 ref_1) ...  (string ref) (string_2 ref_2) ...))
          (store-lookup Σ ref_c))]
  [(class-lookup-mro ((pointer-val ref_c) val_rest ...) string Σ)
   (class-lookup-mro (val_rest ...) string Σ)
   (where (obj-val any_1 any_2 ((string_1 ref_1) ...))
          (store-lookup Σ ref_c))
   (side-condition (not (member (term string) (term (string_1 ...)))))])

(define-metafunction λπ
  class-lookup : val val string Σ -> (Σ val)
  [(class-lookup (pointer-val ref_obj) (obj-val any_c any_mval ((string_1 ref_1) ...  ("__mro__" ref) (string_2 ref_2) ...))
                 string Σ)
   (Σ val_result)
   (where (obj-val any_1 (meta-tuple (val_cls ...)) any_3)
          (fetch-pointer (store-lookup Σ ref) Σ))
   (where val_result
          (class-lookup-mro (val_cls ...) string Σ))])

(define-metafunction λπ
  maybe-bind-method : val val Σ -> (Σ val)
  [(maybe-bind-method (pointer-val ref_obj) (pointer-val ref_result) Σ)
   (Σ_3 (pointer-val ref_method))
   (where (obj-val any_fun (meta-closure (λ (x ...) opt-var_1 e opt-var_2)) ())
    (store-lookup Σ ref_result))
   (where (Σ_1 ref_self) (extend-store Σ (pointer-val ref_obj)))
   (where (Σ_2 ref_func) (extend-store Σ_1 (pointer-val ref_result)))
   (where val_method (obj-val method (no-meta) (("__self__" ref_self) ("__func__" ref_func))))
   (where (Σ_3 ref_method) (extend-store Σ_2 val_method))]
  [(maybe-bind-method (pointer-val ref_obj) val_other Σ)
   (Σ val_other)])
   
(define-metafunction λπ
  subst-exprs : x any (e ...) -> (e ...)
  [(subst-exprs x any ()) ()]
  [(subst-exprs x any (e e_rest ...))
   ((subst-one x any e) e_subs ...)
   (where (e_subs ...) (subst-exprs x any (e_rest ...)))])

(define-metafunction λπ
  subst-fun : x any (x ...) opt-var e opt-var -> e
  [(subst-fun x any (y ...) (x) e opt-var) e]
  [(subst-fun x any (y ...) opt-var e (x)) e]
  [(subst-fun x any (y ...) opt-var_1 e opt-var_2) e
   (side-condition (member (term x) (term (y ...))))]
  [(subst-fun x any (y ...) opt-var_1 e opt-var_2) (subst-one x any e)])

(define-metafunction λπ
  subst-mval : x any mval -> mval
  [(subst-mval x any (meta-num number)) (meta-num number)]
  [(subst-mval x any (meta-str string)) (meta-str string)]
  [(subst-mval x any (meta-list (val ...)))
   (meta-list (subst-exprs x any (val ...)))]
  [(subst-mval x any (meta-tuple (val ...)))
   (meta-tuple (subst-exprs x any (val ...)))]
  [(subst-mval x any (meta-set (val ...)))
   (meta-set (subst-exprs x any (val ...)))]
  [(subst-mval x any (meta-class y)) (meta-class y)] ;; this is a name not a variable
  [(subst-mval x any (meta-closure (λ (y ...) opt-var_1 e opt-var_2)))
   (meta-closure (λ (y ...) opt-var_1 (subst-fun x any (y ...) opt-var_1 e opt-var_2) opt-var_2))]
  [(subst-mval x any (meta-none)) (meta-none)]
  [(subst-mval x any (no-meta)) (no-meta)]
  [(subst-mval x any (meta-port)) (meta-port)])


(define-metafunction λπ
  subst-v : x any val -> val
	[(subst-v x any (obj-val val mval ((string ref) ...)))
   (obj-val (subst-v x any val) (subst-mval x any mval) ((string ref) ...))]
	[(subst-v x any (obj-val y mval ((string ref) ...))) ;; this id is always global, so never subst into it
   (obj-val y (subst-mval x any mval) ((string ref) ...))]
  [(subst-v x any (pointer-val ref)) (pointer-val ref)]
  [(subst-v x any (undefined-val)) (undefined-val)]
  [(subst-v x any (sym string)) (sym string)])

(define-metafunction λπ
  subst-one : x any e -> e
  [(subst-one x any (id x local)) any]
  [(subst-one x any (id y global)) (id y global)] ;; leave globals intact
  [(subst-one x any (id y local)) (id y local)
   (side-condition (not (equal? (term y) (term x))))]
  [(subst-one x any true) true]
  [(subst-one x any false) false]
  [(subst-one x any none) none]
  [(subst-one x any undefined) undefined]
  [(subst-one x any ref) ref]
  [(subst-one x any (fetch e)) (fetch (subst-one x any e))]
  [(subst-one x any (set! e_1 e_2))
   (set! (subst-one x any e_1) (subst-one x any e_2))]
  [(subst-one x any (alloc e)) (alloc (subst-one x any e))]
  [(subst-one x any (object e mval))
   (object (subst-one x any e) (subst-mval x any mval))]
  [(subst-one x any (get-attr e_1 e_2))
   (get-attr (subst-one x any e_1) (subst-one x any e_2))]
  [(subst-one x any (set-attr e_1 e_2 := e_3))
   (set-attr (subst-one x any e_1) (subst-one x any e_2) := (subst-one x any e_3))]
  [(subst-one x any (seq e_1 e_2))
   (seq (subst-one x any e_1) (subst-one x any e_2))]
  [(subst-one x any (assign e_1 := e_2))
   (assign (subst-one x any e_1) := (subst-one x any e_2))]
  [(subst-one x any (if e_1 e_2 e_3))
   (if (subst-one x any e_1)
       (subst-one x any e_2)
       (subst-one x any e_3))]
  [(subst-one x any (let (x local = e_b) in e))
   (let (x local = (subst-one x any e_b)) in e)]
  [(subst-one x any (let (y local = e_b) in e))
   (let (y local = (subst-one x any e_b)) in (subst-one x any e))
   (side-condition (not (equal? (term y) (term x))))]
  [(subst-one x any (let (y global = e_b) in e)) ;; leave globals intact again
   (let (y global = (subst-one x any e_b)) in (subst-one x any e))]
  [(subst-one x any (app e (e_arg ...)))
   (app (subst-one x any e) (subst-exprs x any (e_arg ...)))]
  [(subst-one x any (app e (e_arg ...) e_star))
   (app (subst-one x any e) (subst-exprs x any (e_arg ...)) (subst-one x any e_star))]
  [(subst-one x any (fun (y ...) opt-var_1 e opt-var_2))
   (fun (y ...) opt-var_1 (subst-fun x any (y ...) opt-var_1 e opt-var_2) opt-var_2)]
  [(subst-one x any (while e_1 e_2 e_3))
   (while (subst-one x any e_1)
          (subst-one x any e_2)
          (subst-one x any e_3))]
  [(subst-one x any (loop e)) (loop (subst-one x any e))]
  [(subst-one x any (return e)) (return (subst-one x any e))]
  [(subst-one x any (builtin-prim op (e ...)))
   (builtin-prim op (subst-exprs x any (e ...)))]
  [(subst-one x any (list e_c (e ...)))
   (list (subst-one x any e_c) (subst-exprs x any (e ...)))]
  [(subst-one x any (tuple e_c (e ...)))
   (tuple (subst-one x any e_c) (subst-exprs x any (e ...)))]
  [(subst-one x any (set e_c (e ...)))
   (set (subst-one x any e_c) (subst-exprs x any (e ...)))]
  [(subst-one x any (raise)) (raise)]
  [(subst-one x any (raise e)) (raise (subst-one x any e))]
  [(subst-one x any (tryexcept e_t x e_c e_e)) ;; need to skip catch block if caught
   (tryexcept (subst-one x any e_t)
              x
              e_c
              (subst-one x any e_e))]
  [(subst-one x any (tryexcept e_t y e_c e_e)) 
   (tryexcept (subst-one x any e_t)
              y
              (subst-one x any e_c)
              (subst-one x any e_e))]
  [(subst-one x any (tryfinally e_t e_f))
   (tryfinally (subst-one x any e_t) (subst-one x any e_f))]
  [(subst-one x any break) break]
  [(subst-one x any (module e_p e_b))
   (module (subst-one x any e_p) (subst-one x any e_b))]
  [(subst-one x any (construct-module e))
   (construct-module (subst-one x any e))]
  [(subst-one x any val)
   (subst-v x any val)])

(define-metafunction λπ
  subst : (x ...) (any ...) e -> e
  [(subst () () e) e]
  [(subst (x x_rest ..._1) (any any_rest ..._1) e)
   (subst (x_rest ...) (any_rest ...) (subst-one x any e))])

(define new-loc
  (let ([n 0])
    (lambda () (begin (set! n (add1 n)) n))))
#|
;; simply use this subst function for now
(define-metafunction λπ
  subst : (x ..._1) (any ..._1) e -> e
  [(subst (x ..._1) (any ..._1) e)
   ,(subst/proc (redex-match? λπ x) (term (x ...)) (term (any ...)) (term e))])
|#
(define val? (redex-match? λπ val))

(define-term mt-env (()))
(define-term mt-store ())
