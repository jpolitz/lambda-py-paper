#lang racket/base

(require scriblib/autobib scriblib/bibtex)

(provide generate-bib ~cite)

(define-cite _~cite what-is-this-id-for? generate-bib #:style number-style)

(define db (bibtex-parse (open-input-file "joe.bib")))

(define (~cite key)
  (_~cite (hash-ref (bibdb-bibs db) key (λ () (error 'cite (format "No bib entry: ~a\n" key))))))

