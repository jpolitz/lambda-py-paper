#lang racket

;; This file imports sub-test files.  The imports can be easily commented out
;; to only run subsets of the tests.

(require
 redex
 "lambdapy-basics.rkt"
; "lambdapy-num-tests.rkt"
 "lambdapy-func-tests.rkt"
 "lambdapy-core-tests.rkt"
 "lambdapy-obj-tests.rkt"
 )

(test-results)
