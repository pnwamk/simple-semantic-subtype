#lang typed/racket/base

;; An implementation of the semantic subtyping algorithm
;; in "Covariance and Contravariance: a fresh look at an
;; old issue", section 4 using binary decision diagrams
;; (BDDs) to represent DNF types AND caching of the results
;; of calls to empty-Type?.
;;
;; Note: this is a significant improvement over the version
;; w/o caching on some benchmarks.

(require racket/match
         (only-in racket/unsafe/ops unsafe-fx<)
         "lbdd-lang1.rkt"
         "subtype-test-suite.rkt"
         "tunit.rkt")

(provide (all-defined-out)
         (all-from-out "lbdd-lang1.rkt"))



(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (empty-Type? (Diff t1 t2)))

(define empty-cache : (Weak-HashTable Fixnum Boolean) (make-weak-hasheq))

(: empty-Type? (-> Type Boolean))
(define (empty-Type? t)
  (define h (equal-hash-code t))
  (define cached (hash-ref empty-cache h (λ () 'missing)))
  (cond
    [(eq? 'missing cached)
     (match-define (Type base prod arrow) t)
     (define res
       (and (Bot-base? base)
            (empty-Prod? prod Univ Univ (list))
            (empty-Arrow? arrow Empty (list) (list))))
     (hash-set! empty-cache h res)
     res]
    [else cached]))


(: empty-Prod? (-> (BDD Prod) Type Type (Listof Prod)
                   Boolean))
(define (empty-Prod? t s1 s2 N)
  (match t
    [(? Top?) (or (empty-Type? s1)
                  (empty-Type? s2)
                  (Prod-Phi s1 s2 N))]
    [(? Bot?) #t]
    [(Node (and p (Prod t1 t2)) l u r)
     (and (empty-Prod? l (And s1 t1) (And s2 t2) N)
          (empty-Prod? u s1 s2 N)
          (empty-Prod? r s1 s2 (cons p N)))]))

(: Prod-Phi (-> Type Type (Listof Prod) Boolean))
(define (Prod-Phi s1 s2 N)
  (match N
    [(cons (Prod t1 t2) N)
     (and (let ([s1* (Diff s1 t1)])
            (or (empty-Type? s1*)
                (Prod-Phi s1* s2 N)))
          (let ([s2* (Diff s2 t2)])
            (or (empty-Type? s2*)
                (Prod-Phi s1 s2* N))))]
    [_ #f]))


(: empty-Arrow? (-> (BDD Arrow) Type (Listof Arrow) (Listof Arrow)
                    Boolean))
(define (empty-Arrow? t dom P N)
  (match t
    [(? Top?) (ormap (match-lambda
                       [(Arrow t1 t2)
                        (and (subtype? t1 dom)
                             (Arrow-Phi t1 (Not t2) P))])
                     N)]
    [(? Bot?) #t]
    [(Node (and a (Arrow s1 s2)) l u r)
     (and (empty-Arrow? l (Or s1 dom) (cons a P) N)
          (empty-Arrow? u dom P N)
          (empty-Arrow? r dom P (cons a N)))]))


(: Arrow-Phi (-> Type Type (Listof Arrow)
                 Boolean))
(define (Arrow-Phi t1 t2 P)
  (match P
    [(cons (Arrow s1* s2*) P)
     (let ([t1* (Diff t1 s1*)])
       (and (or (empty-Type? t1*)
                (let ([s2 (And* (map Arrow-rng P))])
                  (subtype? s2 (Not t2))))
            (Arrow-Phi t1 (And t2 s2*) P)
            (Arrow-Phi t1* t2 P)))]
    ;; this last clause was just #t from the paper...?
    [_ (or (empty-Type? t1)
           (empty-Type? t2))]))



(module+ test
  (run-subtype-tests ->Type subtype?)
  )
