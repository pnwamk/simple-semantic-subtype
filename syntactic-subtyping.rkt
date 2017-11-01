#lang typed/racket/base

(require racket/match
         racket/set
         "syntactic-lang.rkt")

(provide (all-defined-out)
         (all-from-out "syntactic-lang.rkt"))

(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (match* (t1 t2)
    [(_ _) #:when (equal? t1 t2) #t]
    [(_ (? Univ?)) #t]
    [((Or ts) t2)
     (for/and : Boolean ([t (in-set ts)])
       (subtype? t t2))]
    [(t1 (Or ts))
     (or (set-member? ts t1)
         (for/or : Boolean ([t (in-set ts)])
           (subtype? t1 t)))]
    [((Prod t1 t2) (Prod s1 s2))
     (and (subtype? t1 s1)
          (subtype? t2 s2))]
    [((Arrow t1 t2) (Arrow s1 s2))
     (and (subtype? s1 t1)
          (subtype? t2 s2))]
    [(_ _) #f]))