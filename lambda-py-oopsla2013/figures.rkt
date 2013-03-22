#lang racket

(require slideshow/pict)
(provide class-scope)

(define outer (linewidth 3 (rectangle 300 250)))
(define deflbl (cc-superimpose (rectangle 40 20) (text "def")))
(define bigbox/lbl (lt-superimpose deflbl outer))

(define classbox (linewidth 2 (rectangle 250 180)))
(define classlbl (cc-superimpose (rectangle 60 20) (text "class")))
(define classbox/lbl (lt-superimpose classlbl classbox))

(define inner (linewidth 2 (rectangle 200 120)))
(define inner/lbl (lt-superimpose deflbl inner))

(define syntactic (cc-superimpose inner/lbl classbox/lbl bigbox/lbl))
(define syntactic/lbl
  (vc-append 10 syntactic (text "Syntactic structure of blocks")))

(define small-classbox (linewidth 2 (rectangle 250 80)))
(define small-classbox/lbl (lt-superimpose classlbl small-classbox))

(define small-inner (linewidth 2 (rectangle 250 80)))
(define small-inner/lbl (lt-superimpose deflbl small-inner))

(define semantic
  (cc-superimpose (vl-append 20 small-inner/lbl small-classbox/lbl)
                  bigbox/lbl))
(define semantic/lbl
  (vc-append 10 semantic (text "Semantic structure of scope")))


(define class-scope (hc-append 30 syntactic/lbl semantic/lbl))