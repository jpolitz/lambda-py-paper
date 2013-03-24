#lang racket

(require slideshow/pict)
(provide class-scope)


(define outer (linewidth 3 (cellophane (colorize (filled-rectangle 110 150) "lightblue") .6)))
(define deflbl (cc-superimpose (rectangle 40 20) (text "def")))
(define bigbox/lbl (lt-superimpose outer deflbl))

(define classbox (linewidth 2 (cellophane (colorize (filled-rectangle 80 100) "red") .5)))
(define classlbl (cc-superimpose (rectangle 60 20) (text "class")))
(define classbox/lbl (lt-superimpose classbox classlbl))

(define inner (linewidth 2 (cellophane (colorize (filled-rectangle 60 50) "darkgreen") .8)))
(define inner/lbl (lt-superimpose inner (colorize deflbl "white")))

(define syntactic (cc-superimpose bigbox/lbl classbox/lbl inner/lbl))
(define syntactic/lbl
  (vc-append 10 syntactic (text "Syntactic structure")))

(define small-classbox (linewidth 2 (cellophane (colorize (filled-rectangle 80 40) "red") .5)))
(define small-classbox/lbl (lt-superimpose small-classbox classlbl))

(define small-inner (linewidth 2 (cellophane (colorize (filled-rectangle 80 40) "darkgreen") .8)))
(define small-inner/lbl (lt-superimpose small-inner (lt-superimpose small-inner (colorize deflbl "white"))))

(define semantic
  (cc-superimpose bigbox/lbl (vl-append 20 small-inner/lbl small-classbox/lbl)
                  ))
(define semantic/lbl
  (vc-append 10 semantic (text "Semantic structure")))

(define class-scope (hc-append 30 syntactic/lbl semantic/lbl))