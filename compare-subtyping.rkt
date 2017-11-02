#lang racket/base

(require "subtype-test-suite.rkt"
         (prefix-in naive: "naive-subtype.rkt")
         (prefix-in lbdd: "lbdd-semantic-subtyping4.rkt")
         (prefix-in syn: "syntactic-subtyping.rkt"))

(provide syntactic/semantic-timing-thunk)


(define syntactic/semantic-timing-thunk
  (λ () (syntactic-subtype-timing 'syntactic
                                  void
                                  syn:->Type
                                  syn:subtype?
                                  'semantic
                                  lbdd:clean-the-cache!
                                  lbdd:->Type
                                  lbdd:subtype?)))


(module+ test
  (syntactic/semantic-timing-thunk))

