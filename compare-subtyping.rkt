#lang typed/racket/base

(require "subtype-test-suite.rkt"
         (prefix-in naive: "naive-subtype.rkt")
         (prefix-in lbdd: "lbdd-semantic-subtyping3.rkt")
         (prefix-in syn: "syntactic-subtyping.rkt"))

(provide syntactic/semantic-timing-thunk)

(: syntactic/semantic-timing-thunk (-> Void))
(define syntactic/semantic-timing-thunk
  (λ () (syntactic-subtype-timing 'syntactic
                                  syn:->Type
                                  syn:subtype?
                                  'semantic
                                  lbdd:->Type
                                  lbdd:subtype?)))

(module+ test
  (syntactic/semantic-timing-thunk))

