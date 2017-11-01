#lang typed/racket/base

(require "subtype-test-suite.rkt"
         (prefix-in naive: "naive-subtype.rkt")
         (prefix-in lbdd: "lazy-bdd-lang3.rkt")
         (prefix-in syn: "syntactic-lang.rkt"))

(provide syntactic/semantic-timing-thunk)

#;(compare-subtype-functions 1000
                           naive:->Type
                           naive:subtype?
                           lbdd:->Type
                           lbdd:subtype?)

(: syntactic/semantic-timing-thunk (-> Void))
(define syntactic/semantic-timing-thunk
  (λ () (syntactic-subtype-timing 'syntactic
                                  syn:->Type
                                  syn:subtype?
                                  'semantic
                                  lbdd:->Type
                                  lbdd:subtype?))) 