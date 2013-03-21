#lang racket

(require redex redex/pict "../redex/lambdapy-core.rkt" "../redex/lambdapy-reduction.rkt")
(provide with-rewriters lp-term lp-term/val lp-reduction lp-metafunction)

(define-syntax-rule (lp-term t)
  (parameterize
     [(default-font-size 11)]
  (with-rewriters
   (λ () (render-term λπ t)))))
(define-syntax-rule (lp-term/val t)
  (parameterize
     [(default-font-size 11)]
  (with-rewriters
   (λ () (term->pict/pretty-write λπ t)))))
(define-syntax-rule (lp-reduction names)
  (parameterize
    [(render-reduction-relation-rules names)
     (default-font-size 11)
     (label-font-size 11)]
    (with-rewriters (lambda ()
      (render-reduction-relation λπ-red #:style 'compact-vertical)))))
(define-syntax-rule (lp-metafunction name cases)
  (with-rewriters
    (lambda ()
      (parameterize
        [(metafunction-cases (if cases cases (metafunction-cases)))
         (metafunction-pict-style 'left-right/compact-side-conditions)
         (metafunction-font-size 11)
         (default-font-size 11)
         (label-font-size 11)]
        (render-metafunction name)))))
(literal-style "Inconsolata")
(paren-style "Inconsolata")
(metafunction-font-size 11)

(define (metafun-rewriter lws)
  (cond
    [(list? lws)
     (define lampart (lw-e (list-ref lws 2)))
     (match lampart
       [(list _ _ args vararg body classarg _)
        (list "λ" args vararg "." body)]
       [else (list lampart)])]
    [else (list lws)]))

(define (rewrite-dict-tuple lws)
  (match (lw-e lws)
    [(? symbol?) (list lws)]
		[(list a b) (list (replace-e a "{}"))]
    [(list _ elts ... _)
     (define (render-dict-elts elts)
      (cond
        [(empty? elts) empty]
        [(empty? (rest elts))
         (render-dict-elt (first elts))]
        [(cons? (rest elts))
         (append (render-dict-elt (first elts))
                 (list ",")
                 (render-dict-elts (rest elts)))]))
     (define (render-dict-elt elt)
       (match (lw-e elt)
        [(list _ key val _)
         (list key ":" val)]
        [_ (list elt)]))
     (flatten (list (list "{") (render-dict-elts elts) (list "}")))]))

(define (replace-e the-lw new-e)
  (lw new-e
      (lw-line the-lw)
      (lw-line-span the-lw)
      (lw-column the-lw)
      (lw-column-span the-lw)
      (lw-unq? the-lw)
      (lw-metafunction? the-lw)))

(define (obj-rewriter lws)
  (match lws
    [(list _ _ cls-or-sym mval dic _)
     (append (list "〈" cls-or-sym "," mval ",")
             (rewrite-dict-tuple dic)
             (list "〉"))]))

(define (pointer-rewriter lws)
  (match lws
    [(list _ _ ref _)
     (list "@" ref)]))

(define (list-literal-rewriter lws)
  (match (lw-e lws)
    [(list a b) (list (replace-e a "[]"))]
    [(list _ elt dots _)
     (list "[" elt dots "]")]
    [(list _ elt1 ... _)
     (append (list "[") elt1 (list "]"))]))

(define (undefined-rewriter _) (list "☠"))

(define (metanum-rewriter lws)
  (match lws [(list _ _ n _) (list "" n "")]))
(define (metastr-rewriter lws)
  (match lws [(list _ _ s _) (list "" s "")]))
(define (metatuple-rewriter lws)
  (match lws [(list _ _ t _) (list "" t "")]))
(define (metalist-rewriter lws)
  (match lws
    [(list _ _ l _) (list-literal-rewriter l)]))
(define (metadict-rewriter lws)
  (match lws
    [(list _ _ d _)
     (append (rewrite-dict-tuple d))]))
(define (metaset-rewriter lws)
  (match lws
    [(list _ _ s _)
     (match (lw-e s)
      [(list _ elt dots _)
       (list "" "{" elt dots "}")])]))
(define (metanone-rewriter _) (list "None"))

(define (id-rewriter lws)
  (match lws
    [(list _ _ x _ _)
     (list "" x "")]))

(define (getfield-rewriter lws)
  (match lws
    [(list _ _ obj fld _)
     (list "" obj "[" fld "]")]))

(define (assign-rewriter lws)
  (match lws
    [(list _ _ target colon val _)
     (list "" target colon val)]
    [else (error 'list (format "Let binder fell through: ~a" (map lw-e lws)))]))

(define (app-rewriter lws)
  (match lws
    [(list _ _ fun args _)
     (list "" fun args "")]
    [(list _ _ fun args vararg _)
     (list "" fun args "*" vararg "")]))

(define (list-rewriter lws)
  (match lws
    [(list _ _ cls lst _)
     (append (list "〈" cls ",")
             (list-literal-rewriter lst)
             (list "〉"))]))

(define (object-rewriter lws)
  (match lws
    [(list _ _ cls _)
     (list "〈" cls "〉")]
    [(list _ _ cls metaval _)
     (list "〈" cls "," metaval "〉")]))

(define (module-rewriter lws)
  (match lws
    [(list _ _ _ body _)
     (list "" body)]))

(define (seq-rewriter lws)
  (match lws
    [(list _ _ e1 e2 _)
     (list "" e1 e2)]))

(define (let-rewriter lws)
  (define (binder-rewriter lw)
    (match (lw-e lw)
      [(list _ var type equals val _)
       (list var "" equals val)]
      [else (error 'list (format "Let binder fell through: ~a" (map lw-e (lw-e lw))))]))
  (match lws
    [(list _ let binder in body _)
     (append (list let)
             (binder-rewriter binder)
             (list in body))]
    [else (error 'list (format "Let fell through: ~a" (map lw-e lws)))]))
     

(define (override-rewriter lws)
  (match lws
    [(list _ _ sto ref val _)
     (list "" sto "[" ref ":=" val "]")]))

(define (extend-rewriter lws)
  (match lws
    [(list _ _ sto val _)
     (list "alloc(" sto "," val ")")]))

(define (store-lookup-rewriter lws)
  (match lws
    [(list _ _ sto ref _)
     (list "" sto "(" ref ")")]))

(define (delta-rewriter lws)
  (match lws
    [(list _ _ op arg ... εs Σ _)
     (append (list "δ(" op) arg (list ")"))]))

(define (with-rewriters thnk)
  (with-compound-rewriters
   (
    ['obj-val obj-rewriter]
    ['pointer-val pointer-rewriter]
    ['undefined-val undefined-rewriter]

    ['meta-num metanum-rewriter]
    ['meta-str metastr-rewriter]
    ['meta-tuple metatuple-rewriter]
    ['meta-list metalist-rewriter]
    ['meta-set metaset-rewriter]
    ['meta-dict metadict-rewriter]
    ['meta-closure metafun-rewriter]
    ['meta-none metanone-rewriter]

    ['id id-rewriter]
    ['get-field getfield-rewriter]
    ['assign assign-rewriter]
    ['app app-rewriter]
    ['object object-rewriter]
    ['list list-rewriter]
    ['module module-rewriter]
    ['seq seq-rewriter]
    ['let let-rewriter]

    ['override-store override-rewriter]
    ['extend-store extend-rewriter]
    ['store-lookup store-lookup-rewriter]
    ['δ delta-rewriter]
   )
   (thnk)))

