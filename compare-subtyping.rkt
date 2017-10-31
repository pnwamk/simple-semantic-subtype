#lang typed/racket/base

(require "subtype-test-suite.rkt"
         (prefix-in naive: "naive-subtype.rkt")
         (prefix-in lbdd: "lazy-bdd-lang3.rkt")
         (prefix-in syn: "syntactic-lang.rkt"))

#;(compare-subtype-functions 1000
                           naive:->Type
                           naive:subtype?
                           lbdd:->Type
                           lbdd:subtype?)

(syntactic-subtype-timing lbdd:->Type
                          lbdd:subtype?
                          syn:->Type
                          syn:subtype?)