#lang racket

(require redex)
(provide with-rewriters)

(define (fun-rewriter lws)
  (define envs (list-ref lws 2))
  (define lampart (lw-e (list-ref lws 3)))
  (define args (list-ref lampart 2))
  (define body (list-ref lampart 4))
  (list "λ" "<" envs ">" args "." body))

(define (rewrite-dict-tuple lws)
  (match lws
    [(list _ init dots _)
     (match (lw-e init)
      [(list _ key val _)
       (list key ":" val "," dots)])]))

(define (lw-loc the-lw [line 0] [column 0])
  (lw (lw-e the-lw)
      (lw-line the-lw)
      (lw-line-span the-lw)
      (lw-column the-lw)
      (lw-column-span the-lw)
      (lw-unq? the-lw)
      (lw-metafunction? the-lw)))

(define (obj-rewriter lws)
  (match lws
    [(list _ _ cls-sym mval dic cls-val _)
     (append (list "〈" cls-sym "," mval "{")
             (rewrite-dict-tuple (lw-e dic))
             (list "}" "@" cls-val "〉"))]
    [(list _ _ cls-sym dic _)
     (list "{" ;"[" cls-sym "," cls-val "," mval "]"
               dic "}")]
    [(list _ _ cls-sym mval dic _)
     (list "{" ;"[" cls-sym "," cls-val "," mval "]"
               dic "}")]))

(define (metanum-rewriter lws)
  (match lws [(list _ _ n _) (list "" n)]))
(define (metastr-rewriter lws)
  (match lws [(list _ _ s _) (list "" s)]))
(define (metatuple-rewriter lws)
  (match lws [(list _ _ t _) (list "" t)]))
(define (metalist-rewriter lws)
  (match lws
    [(list _ _ l _)
     (match (lw-e l)
      [(list _ elt dots _)
       (list "" "[" elt dots "]")])]))
(define (metadict-rewriter lws)
  (match lws
    [(list _ _ d _)
     (append (list "" "{") (rewrite-dict-tuple (lw-e d)) (list "}"))]))
(define (metaset-rewriter lws)
  (match lws
    [(list _ _ s _)
     (match (lw-e s)
      [(list _ elt dots _)
       (list "" "{" elt dots "}")])]))
(define (metanone-rewriter _) (list "None"))

(define (with-rewriters thnk)
  (with-compound-rewriters
   (
    ['fun-val fun-rewriter]
    ['obj-val obj-rewriter]
    ['meta-num metanum-rewriter]
    ['meta-str metastr-rewriter]
    ['meta-tuple metatuple-rewriter]
    ['meta-list metalist-rewriter]
    ['meta-set metaset-rewriter]
    ['meta-dict metadict-rewriter]
    ['meta-none metanone-rewriter]
   )
   (thnk)))

