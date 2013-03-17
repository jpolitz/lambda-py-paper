#lang racket

(require redex)
(provide (all-defined-out))


(define-language λπ
  ;; heap
  (Σ ((ref val) ...))
  ;; type of references
  (ref natural)
  
  ;; environment
  (ε ((x ref) ...))
  (εs (ε ...))
  
  ;; value types
  (val
   (sym string)
	 (obj-val val mval ((string ref) ...))
	 (obj-val x mval ((string ref) ...))
   (fun-val εs (λ (x ...) e))
   (fun-val εs (λ (x ...) (x) e))
   (fun-val εs (λ (x ...) e) x)
   (fun-val εs (λ (x ...) (x) e) x)
   (pointer-val ref)
   (undefined-val))

  ;; primitive operators
  (op string)
  
  ;; id-type
  (t global local)
  
  ;; types of meta-val
  (mval (meta-num number)
        (meta-str string)
        (meta-list (val ...))
        (meta-tuple (val ...))
        ;; set is like a list in representation, lack of order has to be accounted for in semantics
        (meta-set (val ...))
        (meta-class x)
        (meta-none) ;; The Python value
        (no-meta)
        (meta-port)) ;; TODO(dbp): figure out how to represent port
  
  ;; types of expressions
  (e true
     false
     none
     (fetch e)
     (set! e e)
     (alloc e)
     (class x e e)
     (object e mval)
     (get-field e string)
     (seq e e)
     (assign e e)
     (if e e e)
     (id x t)
     (let (x t e) e)
     ;; NOTE(dbp): app with/without stararg
     (app e (e ...))
     (app e (e ...) e)
     ;; NOTE(dbp): 4 variants for presence/absence of stararg, symbol for class
     (fun (x ...) e)
     (fun (x ...) x e)
     (fun (x ...) e x)
     (fun (x ...) x e x)
     (while e e e)
     (loop e) ;; helper syntax for while
     (return e)
     (builtin-prim op (e ...))
     (list e (e ...))
     (tuple e (e ...))
     (set e (e ...))
     ;; NOTE(dbp): empty raise is "reraise"
     (raise)
     (raise e)
     (tryexcept e x e e)
     (tryfinally e e)
     undefined
     break
     (module e e)
     r)
  
  ;; types for result
  (r val
     (return-r val)
     (exception-r val)
     break-r
     continue-r)
  
  ;; evaluation context
  (E hole
     (fetch E)
     (set! E e)
     (set! v E)
     (alloc E)
     (module E e)
     (object E mval)
     (assign e E)
     (seq E e)
     (if E e e)
     (let (x t E) e)
     (list E (e ...))
     (list val E)
     (tuple E (e ...))
     (tuple val E)
     (set E (e ...))
     (set val E)
     (get-field E string)
     (builtin-prim op E)
     (raise E)
     (return E)
     (tryexcept E x e e)
     (tryfinally E e)
     (loop E)
     (app E (e ...))
     (app val E)
     (app E (e ...) e)
     (app val E e)
     (app val (val ...) E)
     (val ... E e ...) ;; for list, tuple, app, etc.
     ;; todo - may need more
     )
  
  ;; context in a try block
  (T hole
     (fetch T)
     (set! T e)
     (set! v T)
     (alloc T)
     (object T mval)
     (assign e T)
     (seq T e)
     (if T e e)
     (let (x t T) e)
     (list T e)
     (list val T)
     (tuple T e)
     (tuple val T)
     (set T e)
     (set val T)
     (get-field T string)
     (builtin-prim op T)
     (raise T)
     (loop T)
     (app T (e ...))
     (app val T)
     (app T (e ...) e)
     (app val T e)
     (app val (val ...) T)
     (val ... T e ...) ;; for list, tuple, app, etc.
     ;; todo - may need more
     )
  
  ;; context for while body
  (H hole
     (fetch H)
     (set! H e)
     (set! v H)
     (alloc H)
     (object H mval)
     (assign e H)
     (seq H e)
     (if H e e)
     (let (x t H) e)
     (list H e)
     (list val H)
     (tuple H e)
     (tuple val H)
     (set H e)
     (set val H)
     (get-field H string)
     (builtin-prim op H)
     (raise H)
     (tryexcept H x e e)
     (tryfinally H e)
     (app H (e ...))
     (app val H)
     (app H (e ...) e)
     (app val H e)
     (app val (val ...) H)
     (val ... H e ...) ;; for list, tuple, app, etc.
     ;; todo - may need more
     )
  
  ;; identifiers, as per
  ;; http://docs.python.org/3.2/reference/lexical_analysis.html#keywords
  (x (variable-except False class finally is return
		      None continue for lambda try
		      True def from nonlocal while
		      and del global not with
		      as elif if or yield
		      assert else import pass
		      break except in raise))
  
  (p (e εs Σ))
  (P (E εs Σ))
  )
