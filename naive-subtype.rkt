#lang typed/racket/base

;; A naive implementation of the semantic subtyping algorithm
;; and DNF representation of set theoretic types presented
;; in "Covariance and Contravariance: a fresh look at an
;; old issue", section 4.
;;
;; i.e. we just use lists and structs to represent the various
;; types and constructors, and we do not use BDDs or the
;; various Φ functions that are given for more efficiently
;; deciding subtyping for products and arrows




(require racket/list
         racket/match
         "simple-lang.rkt"
         "tunit.rkt"
         "subtype-test-suite.rkt")


(provide ->Type subtype?)



(: powerset (All (X) (-> (Listof X) (Listof (Listof X)))))
(define (powerset s)
  (cond
    [(pair? s)
     (define x (car s))
     (define psets (powerset (cdr s)))
     (append psets (map (λ ([pset : (Listof X)]) (cons x pset))
                        psets))]
    [else (list s)]))



(define-type Literal (U Atom (Not Atom)))
(define-predicate Literal? Literal)
(define-type Clause (U Literal (And Literal)))
(define-type DNF (U Clause (Or Clause)))
 
(: ->DNF (-> Type DNF))
(define (->DNF t)
  (match t
    [(? Literal? l) l]
    [(Not (Not inner-t)) (->DNF inner-t)]
    [(Not (And ts)) (DNF-Or-Map (λ ([t : Type]) (->DNF (Not t))) ts)]
    [(Not (Or ts)) (DNF-And-map (λ ([t : Type]) (->DNF (Not t))) ts)]
    [(Or ts) (DNF-Or-Map ->DNF ts)]
    [(And ts) (DNF-And-map ->DNF ts)]))

(: literal-negate (-> Literal Literal))
(define (literal-negate l)
  (match l
    [(? Atom? a) (Not a)]
    [(Not a) a]))

(: DNF-And-map (-> (-> Type DNF) (Listof Type) DNF))
(define (DNF-And-map f ts)
  (let loop ([todo : (Listof Type) ts]
             [ors : (Listof (Or Clause)) (list)]
             [result : (Listof Literal) (list)])
    (match todo
      [(list)
       (let ([result (remove-duplicates result)]
             [ors (remove-duplicates ors)])
         (match ors
           [(list) (if (= 1 (length result))
                       (car result)
                       (And result))]
           [(cons (Or or-ts) rst)
            (define and-ts (append rst result))
            (->DNF (Or (map (λ ([t : Type]) (And (cons t and-ts)))
                            or-ts)))]))]
      [(cons (app f t) rst)
       (match t
         [(? Literal? l)
          (loop rst ors (cons l result))]
         [(And ls)
          (loop rst ors (append ls result))]
         [(? Or? d)
          (loop rst (cons d ors) result)])])))

(: DNF-Or-Map (-> (-> Type DNF) (Listof Type) DNF))
(define (DNF-Or-Map f ts)
  (let loop ([todo : (Listof Type) ts]
             [result : (Listof Clause) (list)])
    (match todo
      [(list) (let ([result (remove-duplicates result)])
                (if (= 1 (length result))
                    (first result)
                    (Or result)))]
      [(cons (app f d) rst)
       (cond
         [(Or? d) (loop rst (append (Or-ts d) result))]
         [else (loop rst (cons d result))])])))

(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (empty-DNF?
   (->DNF (And (list t1 (Not t2))))))

(: empty-DNF? (-> DNF Boolean))
(define (empty-DNF? d)
  (match d
    [(? Literal? l) (empty-DNF-clause? l)]
    [(? And? clause) (empty-DNF-clause? clause)]
    [(Or cs) (andmap empty-DNF-clause? cs)]))

(: empty-DNF-clause? (-> Clause Boolean))
(define (empty-DNF-clause? clause)
  (match clause
    [(? Literal? l) (empty-DNF-clause? (And (list l)))]
    [(And ls)
     (define P (filter Atom? ls))
     (define-values (Ptag Pprod Parrow)
       (extract-positive-literals P))
     (cond
       [(not (null? Ptag))
        (cond
          [(or (not (null? Pprod))
               (not (null? Parrow)))
           #t]
          [else
           (uninhabitited-Tag-clause? Ptag (filter Not-Tag? ls))])]
       [(not (null? Pprod))
        (cond
          [(not (null? Parrow)) #t]
          [else
           (uninhabitited-Prod-clause? Pprod (filter Not-Prod? ls))])]
       [(not (null? Parrow))
        (uninhabitited-Arrow-clause? Parrow (filter Not-Arrow? ls))]
       [else #f])]))

(: extract-positive-literals (-> (Listof Atom)
                                 (values (Listof Tag)
                                         (Listof Prod)
                                         (Listof Arrow))))
(define (extract-positive-literals P)
  (let loop : (values (Listof Tag)
                      (Listof Prod)
                      (Listof Arrow))
    ([todo : (Listof Atom) P]
     [Ptag : (Listof Tag) (list)]
     [Pprod : (Listof Prod) (list)]
     [Parrow : (Listof Arrow) (list)])
    (match todo
      [(list) (values Ptag Pprod Parrow)]
      [(cons a as)
       (cond
         [(Tag? a) (loop as (cons a Ptag) Pprod Parrow)]
         [(Prod? a) (loop as Ptag (cons a Pprod) Parrow)]
         [else (loop as Ptag Pprod (cons a Parrow))])])))


(: uninhabitited-Tag-clause?
   (-> (Listof Tag) (Listof (Not Tag)) Boolean))
(define (uninhabitited-Tag-clause? P N)
  (cond
    [(< 1 (length (remove-duplicates P)))
     #true]
    [else
     (ormap (λ ([n : (Not Tag)]) (and (member (Not-t n) P) #t))
            N)]))


(: uninhabitited-Prod-clause?
   (-> (Listof Prod) (Listof (Not Prod)) Boolean))
(define (uninhabitited-Prod-clause? P N)
  (let ([s1 (And (map Prod-l P))]
        [s2 (And (map Prod-r P))])
    (andmap
     (λ ([N* : (Listof (Not Prod))])
       (or (let ([t1 (Or (map (λ ([p : (Not Prod)])
                                (Prod-l (Not-t p)))
                              N*))])
             (subtype? s1 t1))
           (let* ([N-N* (remove* N* N)]
                  [t2 (Or (map (λ ([p : (Not Prod)])
                                 (Prod-r (Not-t p)))
                               N-N*))])
             (subtype? s2 t2))))
     (powerset N))))



(: uninhabitited-Arrow-clause?
   (-> (Listof Arrow) (Listof (Not Arrow)) Boolean))
(define (uninhabitited-Arrow-clause? P N)
  (let ([dom (Or (map Arrow-dom P))])
    (ormap (λ ([na : (Not Arrow)])
             (let ([t1 (Arrow-dom (Not-t na))]
                   [t2 (Arrow-rng (Not-t na))])
               (and (subtype? t1 dom)
                    (andmap (λ ([P* : (Listof Arrow)])
                              (or (let ([s1 (Or (map Arrow-dom P*))])
                                    (subtype? t1 s1))
                                  (let ([s2 (And (map Arrow-rng (remove* P* P)))])
                                    (subtype? s2 t2))))
                            (remove P (powerset P))))))
           N)))

(module+ test
  (run-subtype-tests ->Type subtype?))

;(module+ benchmark
;  (run-subtype-benchmark "naive" subtype?))

