#lang typed/racket/base

(require "subtype-test-suite.rkt"
         (prefix-in naive: "naive-subtype.rkt")
         (prefix-in lbdd: "lazy-bdd-lang3.rkt"))

(compare-subtype-functions 1000
                           naive:->Type
                           naive:subtype?
                           lbdd:->Type
                           lbdd:subtype?)