#lang racket

(require redex)
;(require redex/tut-subst)
(require "lambdapy-core.rkt"
         "lambdapy-prim.rkt")

(provide λπ-red override-store class-lookup class-lookup-mro maybe-bind-method)


(define λπ-red
  (reduction-relation
   λπ
   #:domain p
   (==> none
        vnone
        "none")
   (==> undefined
        (undefined-val)
        "undefined")
   (==> true
	vtrue
	"true")
   (==> false
	vfalse
	"false")
   (--> ((in-hole E (list val_c (val ...))) εs Σ)
        ((in-hole E (pointer-val ref_new)) εs Σ_1)
        "E-List"
        (where (Σ_1 ref_new) (extend-store Σ (obj-val val_c (meta-list (val ...)) ()))))
   (--> ((in-hole E (tuple val_c (val ...))) εs Σ)
        ((in-hole E (pointer-val ref_new)) εs Σ_1)
        "E-Tuple"
        (where (Σ_1 ref_new) (extend-store Σ (obj-val val_c (meta-tuple (val ...)) ()))))
   (--> ((in-hole E (set val_c (val ...))) εs Σ)
        ((in-hole E (pointer-val ref_new)) εs Σ_1)
        "E-Set"
        (where (Σ_1 ref_new) (extend-store Σ (obj-val val_c (meta-set (val ...)) ()))))
   (--> ((in-hole E (fetch (pointer-val ref))) εs Σ)
        ((in-hole E (store-lookup Σ ref)) εs Σ)
        "E-Fetch")
   (--> ((in-hole E (set! (pointer-val ref) val)) εs Σ)
        ((in-hole E val) εs Σ_1)
        "E-Set!"
        (where Σ_1 (override-store Σ ref val)))
   (--> ((in-hole E (alloc val)) εs Σ)
        ((in-hole E (pointer-val val)) εs Σ_1)
        "E-Alloc"
        (where (Σ_1 ref_new) (extend-store Σ val)))
   (--> ((in-hole E (fun (x ...) opt-var_1 e opt-var_2)) εs Σ)
        ((in-hole E (pointer-val ref_fun)) εs Σ_1)
        (where (Σ_1 ref_fun)
          (extend-store Σ (obj-val '%function
                                   (meta-fun εs (λ (x ...) opt-var_1 e opt-var_2))
                                   ())))
        "E-Fun")
   (--> ((in-hole E (object val mval)) εs Σ)
        ((in-hole E (pointer-val ref_new)) εs Σ_1)
        "E-Object"
        (where ref_new (get-new-loc Σ))
        (where Σ_1 (override-store Σ ref_new (obj-val val mval ()))))
   (--> ((in-hole E (prim1 op val)) εs Σ)
        ((in-hole E (δ op val εs Σ)) εs Σ)
        "prim1")
   (--> ((in-hole E (prim2 op val_1 val_2)) εs Σ)
        ((in-hole E (δ op val_1 val_2 εs Σ)) εs Σ)
        "prim2")
   (--> ((in-hole E (builtin-prim op (val ...))) εs Σ)
        ((in-hole E (δ op val ... εs Σ)) εs Σ)
        "builtin-prim")
   (==> (if val e_1 e_2)
        e_1
        (side-condition (term (truthy? val)))
        "if-true")
   (==> (if val e_1 e_2)
        e_2
        (side-condition (not (term (truthy? val))))
        "if-false")
   (==> (seq val e)
        e
        "E-Seq")
   ;; NOTE(yao): this may be unnecessary, since context T deals with it
   ;; I wrote it and then deleted.
   ;; same thing for "seq-return" etc., if we use context to do it
   #|
   (==> (if (exception-r val) e_1 e_2)
	(exception-r val)
	"if-exception")|#
   (==> (seq (return-r val) e)
	(return-r val)
	"seq-return")
   (==> (seq (exception-r val) e)
        (exception-r val))
   #|
   (==> (seq break-r e)
	break-r
	"seq-break")
   (==> (seq (exception-r val) e)
	(exception-r val)
	"seq-exception")|#
   (==> (while e_1 e_2 e_3)
        ;(loop (if e_1 (seq e_2 (while e_1 e_2 e_3)) e_3))
        (if e_1 (loop (seq e_2 (while e_1 e_2 e_3))) e_3)
        "while")
   (==> (loop val)
        vnone
        "loop")
   (==> (loop (in-hole H break-r))
        break-r
        "loop-break")
   (==> break
        break-r
        "break")
   (==> (return val)
	(return-r val)
	"return")
   (==> (raise val)
        (exception-r val)
        "raise") ;; TODO: check type of val
   (==> (try val (e_exc ...) val_else e_finally)
        e_finally
        "try-noexc")
   (==> (try val (e_exc ...) e_else e_finally)
        (try e_else () vnone e_finally)
        (side-condition (not (val? (term e_else))))
        "try-else")
   (==> (try (in-hole T (exception-r val)) () e_else e_finally)
        (seq e_finally (exception-r val))
        "try-exc-nohandler")
   (==> (try (in-hole T (exception-r val)) ((except () e) e_exc ...) e_else e_finally)
        (try e () vnone e_finally)
        "try-exc-notype")
   (==> (try (in-hole T (exception-r val)) ((except () (x) e) e_exc ...) e_else e_finally)
        (try (let (x val) e) () vnone e_finally)
        "try-exc-notype-named")
   (==> (try (in-hole T (exception-r val)) ((except (e_type1 e_type ...) e) e_exc ...) e_else e_finally)
        (try (if (builtin-prim "isinstance" (val e_type1)) ;; in principle "isinstance" should handle tuple (tuple (e_type1 e_type ...))
                 e
                 (try (in-hole T (exception-r val)) (e_exc ...) e_else vnone))
             () vnone e_finally)
        "try-exc-type")
   (==> (try (in-hole T (exception-r val)) ((except (e_type1 e_type ...) (x) e) e_exc ...) e_else e_finally)
        (try (if (builtin-prim "isinstance" (val e_type1)) ;; in principle "isinstance" should handle tuple (tuple (e_type1 e_type ...))
                 (let (x val) e)
                 (try (in-hole T (exception-r val)) (e_exc ...) e_else vnone))
             () vnone e_finally)
        "try-exc-type-named")
   (==> (try (in-hole T r) (e_exc ...) e_else e_finally)
        (seq e_finally r)
        (side-condition (not (val? (term r))))
        (side-condition (not (redex-match? λπ (exception-r any) (term r))))
        "try-nonval")
   ;; NOTE(dbp): I don't think this is the correct behavior - uncaught exceptions
   ;; should percolate up as (exception-r val) results, NOT cause racket errors.
   ;;    agreed. (exception-r val) should be the reduction result. -yao
   (--> ((in-hole T (exception-r val)) εs Σ)
        ((exception-r val) εs Σ)
        (side-condition (not (redex-match? λπ hole (term T)))) ;; avoid cycle
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
   (--> ((in-hole E (let (x_1 local val_1) e))
         (ε_1 ε ...)
         Σ)
        ((in-hole E e)
         ((extend-env ε_1 x_1 ref_1) ε ...) ;; let-body's env will leak out, but it seems interp does it
         (override-store Σ ref_1 val_1))
        (where ref_1 ,(new-loc))
        "let")
   (--> ((in-hole E (let (x_1 local (return-r val_1)) e))
         (ε_1 ε ...)
         Σ)
        ((in-hole E e)
         ((extend-env ε_1 x_1 ref_1) ε ...)
         (override-store Σ ref_1 val_1))
        (where ref_1 ,(new-loc))
        "let-ret")
   (--> ((in-hole E (let (x_1 local break-r) e))
         (ε_1 ε ...)
         Σ)
        ((in-hole E e)
         ((extend-env ε_1 x_1 ref_1) ε ...)
         (override-store Σ ref_1 vnone))
        (where ref_1 ,(new-loc))
        "let-brk")
   #|
   (==> (let (x_1 (exception-r val)) e_1)
        (exception-r val)
        "let-exc")|#
   (--> ((in-hole E (id x_1 local))
         (name env (((x_2 ref_2) ... (x_1 ref_1) (x_3 ref_3) ...) ε ...))
         (name store ((ref_4 val_4) ... (ref_1 val_1) (ref_5 val_5) ...)))
        ((in-hole E val_1)
         env
         store)
        (side-condition (not (member (term x_1) (term (x_2 ... x_3 ...)))))
        (side-condition (not (member (term ref_1) (term (ref_4 ... ref_5 ...)))))
        (side-condition (not (redex-match? λπ (undefined-val) (term val_1)))) ;; TODO: exception for undefined
        "id-local")
   (--> ((in-hole E (get-field (pointer-val ref) string_1)) εs Σ)
        ((in-hole E (store-lookup Σ ref_1)) εs Σ)
        (where (obj-val x mval ((string_2 ref_2) ... (string_1 ref_1) (string_3 ref_3) ...)) (store-lookup Σ ref))
        "E-GetField")
   (--> ((in-hole E (get-field (pointer-val ref_obj) string)) εs Σ)
        ((in-hole E val_result) εs Σ_result)
        (where (obj-val (pointer-val ref) mval ((string_1 ref_2) ...))
               (store-lookup Σ ref_obj))
        (where (Σ_result val_result)
          (class-lookup (pointer-val ref_obj) (store-lookup Σ ref) string Σ))
        "E-GetField-Class")
   (--> ((in-hole E (get-field (obj-val x mval ((string_2 ref_2) ... ("__class__" ref_1) (string_3 ref_3) ...)) string_1))
         εs
         (name store ((ref_4 val_4) ... (ref_1 val_1) (ref_5 val_5) ...)))
        ((in-hole E (get-field val_1 string_1))
         εs
         store)
        (side-condition (not (string=? "__class__" (term string_1))))
        (side-condition (not (member (term string_1) (term (string_2 ... string_3 ...)))))
        (side-condition (not (member "__class__" (term (string_2 ... string_3 ...)))))
        (side-condition (not (member (term ref_1) (term (ref_4 ... ref_5 ...)))))
        "get-field-class")
   (--> ((in-hole E (get-field (obj-val x_base mval ((string_2 ref_2) ...)) string_1))
         (name env (((x_1 ref_x1) ...) ... ((x_2 ref_x2) ... (x_base ref_base) (x_3 ref_x3) ...) ε ...))
         (name store ((ref_4 val_4) ... (ref_base val_base) (ref_5 val_5) ...)))
        ((in-hole E (get-field val_base string_1))
         env
         store)
        (side-condition (not (member (term string_1) (term (string_2 ...)))))
        (side-condition (not (member "__class__" (term (string_2 ...)))))
        (side-condition (not (member (term x_base) (append* (term ((x_1 ...) ...))))))
        (side-condition (not (member (term x_base) (term (x_2 ... x_3 ...)))))
        (side-condition (not (member (term ref_base) (term (ref_4 ... ref_5 ...)))))
        "get-field-base")
   (--> ((in-hole E (assign (id x_1 local) val_1))
         ((name scope ((x_2 ref_2) ...)) ε ...)
         Σ)
        ((in-hole E vnone)
         ((extend-env scope x_1 ref_1) ε ...)
         (override-store Σ ref_1 val_1))
        (side-condition (not (member (term x_1) (term (x_2 ...)))))
        (where ref_1 ,(new-loc))
        "assign-local-free")
   (--> ((in-hole E (assign (id x_1 local) val_1))
         (name env (((x_2 ref_2) ... (x_1 ref_1) (x_3 ref_3) ...) ε ...))
         Σ)
        ((in-hole E vnone)
         env
         (override-store Σ ref_1 val_1))
        (side-condition (not (member (term x_1) (term (x_2 ... x_3 ...)))))
        "assign-local-bound")
   (--> ((in-hole E (assign (get-field (obj-val x mval ((string_2 ref_2) ... (string_1 ref_1) (string_3 ref_3) ...)) string_1) val_1)) εs Σ)
        ((in-hole E vnone) εs (override-store Σ ref_1 val_1))
        (side-condition (not (member (term string_1) (term (string_2 ... string_3 ...)))))
        "E-AssignUpdate")
   (--> ((in-hole E (assign (get-field (obj-val x mval ((string ref) ... )) string_1) val_1)) εs Σ)
        ((in-hole E (obj-val x mval ((string_1 ref_new) (string ref) ...))) εs Σ_1)
        (side-condition (not (member (term string_1) (term (string ...)))))
        "E-AssignAdd"
        (where (Σ_1 ref_new) (extend-store Σ val_1)))
   (==> (val ... r e ...)
        (r)
        (side-condition (not (val? (term r))))
        (side-condition (not (and (empty? (term (val ...))) (empty? (term (e ...))))))
        "cascade-nonval")
   with
   [(--> (in-hole P e_1) (in-hole P e_2))
    (==> e_1 e_2)]
   ))

(define new-loc
  (let ([n 0])
    (lambda () (begin (set! n (add1 n)) n))))

(define-metafunction λπ
  extend-env : ε x ref -> ε
  [(extend-env ((x_2 ref_2) ...) x_1 ref_1) ((x_2 ref_2) ... (x_1 ref_1))])

(define-metafunction λπ
  override-store : Σ ref val -> Σ
  [(override-store ((ref_2 val_2) ...) ref_1 val_1)
   ((ref_2 val_2) ... (ref_1 val_1))
   (side-condition (not (member (term ref_1) (term (ref_2 ...)))))]
  [(override-store ((ref_2 val_2) ... (ref_1 val_0) (ref_3 val_3) ...) ref_1 val_1)
   ((ref_2 val_2) ... (ref_1 val_1) (ref_3 val_3) ...)
   (side-condition (not (member (term ref_1) (term (ref_2 ...)))))])
 
(define-metafunction λπ
  extend-store : Σ val -> (Σ ref)
  [(extend-store (name Σ ((ref val) ...)) val_new)
   (((ref val) ... (ref_new val_new)) ref_new)
   (where ref_new (get-new-loc Σ))])

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
   (maybe-bind-method (pointer-val ref_obj) val_result Σ)
   (where (obj-val any_1 (meta-tuple (val_cls ...)) any_3)
          (fetch-pointer (store-lookup Σ ref) Σ))
   (where val_result
          (class-lookup-mro (val_cls ...) string Σ))])

(define-metafunction λπ
  maybe-bind-method : val val Σ -> (Σ val)
  [(maybe-bind-method (pointer-val ref_obj) (pointer-val ref_result) Σ)
   (Σ_3 (pointer-val ref_method))
   (where (obj-val any_fun (meta-closure εs (λ (x ...) opt-var_1 e opt-var_2)) ())
    (store-lookup Σ ref_result))
   (where (Σ_1 ref_self) (extend-store Σ (pointer-val ref_obj)))
   (where (Σ_2 ref_func) (extend-store Σ_1 (pointer-val ref_result)))
   (where val_method (obj-val method (no-meta) (("__self__" ref_self) ("__func__" ref_func))))
   (where (Σ_3 ref_method) (extend-store Σ_2 val_method))]
  [(maybe-bind-method (pointer-val ref_obj) val_other Σ)
   (Σ val_other)])
   

(define-metafunction λπ
  fetch-pointer : val Σ -> val
  [(fetch-pointer (pointer-val ref) Σ) (store-lookup Σ ref)])

(define-metafunction λπ
  store-lookup : Σ ref -> val
  [(store-lookup ((ref_1 val_1) ... (ref val) (ref_n val_n) ...) ref)
   val])

(define-metafunction λπ
  get-new-loc : Σ -> ref
  [(get-new-loc ((ref_1 val_1) ...))
   ,(add1 (apply max (cons 0 (term (ref_1 ...)))))])


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
