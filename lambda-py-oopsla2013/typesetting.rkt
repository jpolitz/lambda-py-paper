#lang racket

(require redex "../redex/lambdapy-core.rkt" "../redex/lambdapy-reduction.rkt")
(provide with-rewriters lp-term lp-reduction)

(define-syntax-rule (lp-term t)
  (parameterize
     [(default-font-size 11)]
  (with-rewriters
   (λ () (render-term λπ t)))))
(define-syntax-rule (lp-reduction names)
  (parameterize
    [(render-reduction-relation-rules names)
     (default-font-size 11)]
    (with-rewriters (lambda ()
      (render-reduction-relation λπ-red #:style 'compact-vertical)))))
(literal-style "Inconsolata")
(paren-style "Inconsolata")

(define (fun-rewriter lws)
  (define envs (list-ref lws 2))
  (define lampart (lw-e (list-ref lws 3)))
  (match lampart
    [(list _ _ args body _)
     (list "λ" "<" envs ">" args "." body)]
    [(list _ _ args vararg body _)
     (list "λ" "<" envs ">" args vararg "." body)]))

(define (rewrite-dict-tuple lws)
  (match lws
		[(list a b) (list "{}")]
    [(list _ init dots _)
     (match (lw-e init)
      [(list _ key val _)
       (list "{" key ":" val "," dots "}")])]))

(define (lw-loc the-lw new-e [line 0] [column 0])
  (lw (lw-e new-e)
      (lw-line the-lw)
      (lw-line-span the-lw)
      (lw-column the-lw)
      (lw-column-span the-lw)
      (lw-unq? the-lw)
      (lw-metafunction? the-lw)))

(define (obj-rewriter lws)
  (match lws
    [(list _ _ cls-or-sym mval dic _)
     (append (list "〈" cls-or-sym "," mval)
             (rewrite-dict-tuple (lw-e dic))
             (list "〉"))]))

(define (pointer-rewriter lws)
  (match lws
    [(list _ _ ref _)
     (list "@" ref)]))

(define (list-literal-rewriter lws)
  (match lws
    [(list _ _) (list "[]")]
    [(list _ elt dots _)
     (list "[" elt dots "]")]))

(define (undefined-rewriter _) (list "☠"))

(define (metanum-rewriter lws)
  (match lws [(list _ _ n _) (list "" n "")]))
(define (metastr-rewriter lws)
  (match lws [(list _ _ s _) (list "" s "")]))
(define (metatuple-rewriter lws)
  (match lws [(list _ _ t _) (list "" t "")]))
(define (metalist-rewriter lws)
  (match lws
    [(list _ _ l _) (list-literal-rewriter (lw-e l))]))
(define (metadict-rewriter lws)
  (match lws
    [(list _ _ d _)
     (append (rewrite-dict-tuple (lw-e d)))]))
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

(define (app-rewriter lws)
  (match lws
    [(list _ _ fun args _)
     (list "" fun args "")]))

(define (list-rewriter lws)
  (match lws
    [(list _ _ cls lst _)
     (append (list "" cls ":") (list-literal-rewriter (lw-e lst)))]))

(define (object-rewriter lws)
  (match lws
    [(list _ _ cls _)
     (list "" cls "〈〉" "")]
    [(list _ _ cls metaval _)
     (list "" cls "〈" metaval "〉" "")]))

(define (override-rewriter lws)
  (match lws
    [(list _ _ sto ref val _)
     (list "" sto "[" ref ":=" val "]")]))

(define (with-rewriters thnk)
  (with-compound-rewriters
   (
    ['fun-val fun-rewriter]
    ['obj-val obj-rewriter]
    ['pointer-val pointer-rewriter]
    ['undefined-val undefined-rewriter]

    ['meta-num metanum-rewriter]
    ['meta-str metastr-rewriter]
    ['meta-tuple metatuple-rewriter]
    ['meta-list metalist-rewriter]
    ['meta-set metaset-rewriter]
    ['meta-dict metadict-rewriter]
    ['meta-none metanone-rewriter]

    ['id id-rewriter]
		['get-field getfield-rewriter]
		['app app-rewriter]
		['object object-rewriter]
		['list list-rewriter]

    ['override-store override-rewriter]
   )
   (thnk)))

