#lang typed/racket/base

(require racket/match
         "base-lang.rkt")

(def-struct Top ())
(def-struct Bot ())
(def-struct Node ([atom : Atom] [lchild : BDD] [rchild : BDD]))
(define-type BDD (U Top Bot Node))

(define tt (Top))
(define ff (Bot))

(: BDD->Atom (-> BDD Atom))
(define (BDD->Atom b)
  (match b
    [(? Bot?) Empty]
    [(? Top?) Univ]
    [(Node a l r) ]))