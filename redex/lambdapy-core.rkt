#lang racket

(require redex)
(provide (all-defined-out))


(define-language λπ
  ;; heap
  (Σ ((ref v+undef) ...))
  ;; type of references
  (ref natural)
  
  ;; environment
  (ε ((x ref) ...))
  
  ;; value types
  ((v val)
	 (obj-val val mval ((string ref) ...))
	 (obj-val x mval ((string ref) ...))
   (pointer-val ref)
   (sym string))
  (v+undef v (undefined-val))

  ;; primitive operators
  (op string)
  
  ;; id-type
  (t global local)
  
  ;; types of meta-val
  (mval (meta-num number)
        (meta-str string)
        (meta-list (val ...))
        (meta-tuple (val ...))
        (meta-set (val ...))
        (meta-class x)
        (meta-closure (λ (x ...) opt-var e opt-var))
        (meta-none) ;; The Python value
        (no-meta)
        (meta-port)) ;; TODO(dbp): figure out how to represent port

  (opt-var (x) (no-var))
  
  ;; types of expressions
  (e true
     false
     none
     ref
     (fetch e)
     (set! e e)
     (alloc e)
     (class x e e)
     (object e mval)
     (get-field e string)
     (get-attr e e)
     (seq e e)
     (assign e := e)
     (if e e e)
     (id x t)
     (let (x t = e) in e)
     ;; NOTE(dbp): app with/without stararg
     (app e (e ...))
     (app e (e ...) e)
     ;; NOTE(dbp): 4 variants for presence/absence of stararg, symbol for class
     (fun (x ...) opt-var e opt-var)
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
     (construct-module e)
     (err val)
     v+undef)
  
  ;; evaluation context
  (E hole
     (fetch E)
     (set! E e)
     (set! val E)
     (alloc E)
     (module E e)
     (object E mval)
     (assign (get-field E string) := e)
     (assign ref := E)
     (assign (get-field val string) := E)
     (assign (id x global) := E)
     (seq E e)
     (if E e e)
     (let (x t = E) in e)
     (list E (e ...))
     (list val E)
     (tuple E (e ...))
     (tuple val E)
     (set E (e ...))
     (set val E)
     (get-field E string)
     (get-attr E e)
     (get-attr val E)
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
  
  ;; context in a try/finally block
  (F hole
     (fetch F)
     (set! F e)
     (set! val F)
     (alloc F)
     (object F mval)
     (assign (get-field F string) := e)
     (assign ref := F)
     (assign (get-field val string) := F)
     (assign (id x global) := F)
     (seq F e)
     (if F e e)
     (let (x t = F) in e)
     (list F e)
     (list val F)
     (tuple F e)
     (tuple val F)
     (set F e)
     (set val F)
     (get-field F string)
     (get-attr F e)
     (get-attr val F)
     (builtin-prim op F)
     (raise F)
     (loop F)
     (app F (e ...))
     (app val F)
     (app F (e ...) e)
     (app val F e)
     (app val (val ...) F)
     (tryexcept F x e e)
     (val ... F e ...) ;; for list, tuple, app, etc.
     )
  ;; context in a try block
  (T hole
     (fetch T)
     (set! T e)
     (set! val T)
     (alloc T)
     (object T mval)
     (assign (get-field T string) := e)
     (assign ref := T)
     (assign (get-field val string) := T)
     (assign (id x global) := T)
     (seq T e)
     (if T e e)
     (let (x t = T) in e)
     (list T e)
     (list val T)
     (tuple T e)
     (tuple val T)
     (set T e)
     (set val T)
     (get-field T string)
     (get-attr T e)
     (get-attr val T)
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
     (set! val H)
     (alloc H)
     (object H mval)
     (assign (get-field H string) := e)
     (assign ref := H)
     (assign (get-field val string) := H)
     (assign (id x global) := H)
     (seq H e)
     (if H e e)
     (let (x t = H) in e)
     (list H e)
     (list val H)
     (tuple H e)
     (tuple val H)
     (set H e)
     (set val H)
     (get-field H string)
     (get-attr H e)
     (get-attr val H)
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
  
  ;; contexts for returning
  (R hole
     (fetch R)
     (set! R e)
     (set! val R)
     (alloc R)
     (object R mval)
     (assign (get-field R string) := e)
     (assign ref := R)
     (assign (get-field val string) := R)
     (assign (id x global) := R)
     (seq R e)
     (if R e e)
     (let (x t = R) in e)
     (list R e)
     (list val R)
     (tuple R e)
     (tuple val R)
     (set R e)
     (set val R)
     (get-field R string)
     (get-attr R e)
     (get-attr val R)
     (builtin-prim op R)
     (raise R)
     (loop R) ;; DO go into active loops to find returns
     (tryexcept R x e e) ;; DO go into try/catches to find returns
     ;; (tryfinally R e) DON'T go into tryfinallys to find returns
     (app R (e ...))
     (app val R)
     (app R (e ...) e)
     (app val R e)
     (app val (val ...) R)
     (val ... R e ...) ;; for list, tuple, app, etc.
     ;; todo - may need more
     )

  ;; identifiers, as per
  ;; http://docs.python.org/3.2/reference/lexical_analysis.html#keywords
  ((w x y z f g h) (variable-except λ δ))
  
  (p (e ε Σ))
  (P (E ε Σ))
  )
