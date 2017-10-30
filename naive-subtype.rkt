#lang typed/racket/base

(require racket/list
         racket/match
         "simple-lang.rkt"
         "list-set-utils.rkt"
         "tunit.rkt"
         "subtype-test-suite.rkt")


(provide ->Type subtype?)

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

(: DNF-And-map (-> (-> Type DNF) (Setof Type) DNF))
(define (DNF-And-map f ts)
  (let loop ([todo : (Setof Type) ts]
             [ors : (Setof (Or Clause)) (set)]
             [result : (Setof Literal) (set)])
    (match todo
      [(list)
       (match ors
         [(list) (if (= 1 (set-count result))
                     (car result)
                     (And result))]
         [(cons (Or or-ts) rst)
          (define and-ts (append rst result))
          (->DNF (Or (map (λ ([t : Type]) (And (set-add and-ts t)))
                          or-ts)))])]
      [(cons (app f t) rst)
       (match t
         [(? Literal? l)
          (loop rst ors (set-add result l))]
         [(And ls)
          (loop rst ors (append ls result))]
         [(? Or? d)
          (loop rst (set-add ors d) result)])])))

(: DNF-Or-Map (-> (-> Type DNF) (Setof Type) DNF))
(define (DNF-Or-Map f ts)
  (let loop ([todo : (Setof Type) ts]
             [result : (Setof Clause) (set)])
    (match todo
      [(list) (if (= 1 (set-count result))
                  (first result)
                  (Or result))]
      [(cons (app f d) rst)
       (cond
         [(Or? d) (loop rst (append (Or-ts d) result))]
         [else (loop rst (set-add result d))])])))

(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (empty-DNF?
   (->DNF (And (set t1 (Not t2))))))

(: empty-DNF? (-> DNF Boolean))
(define (empty-DNF? d)
  (match d
    [(? Literal? l) (empty-DNF-clause? l)]
    [(? And? clause) (empty-DNF-clause? clause)]
    [(Or cs) (forall empty-DNF-clause? cs)]))

(: empty-DNF-clause? (-> Clause Boolean))
(define (empty-DNF-clause? clause)
  (match clause
    [(? Literal? l) (empty-DNF-clause? (And (list l)))]
    [(And ls)
     (define P (filter Atom? ls))
     (define-values (Ptag Pprod Parrow)
       (extract-positive-literals P))
     (cond
       [(non-empty-set? Ptag)
        (cond
          [(or (non-empty-set? Pprod)
               (non-empty-set? Parrow))
           #t]
          [else
           (uninhabitited-Tag-clause? Ptag (filter Not-Tag? ls))])]
       [(non-empty-set? Pprod)
        (cond
          [(non-empty-set? Parrow) #t]
          [else
           (uninhabitited-Prod-clause? Pprod (filter Not-Prod? ls))])]
       [(non-empty-set? Parrow)
        (uninhabitited-Arrow-clause? Parrow (filter Not-Arrow? ls))]
       [else #f])]))

(: extract-positive-literals (-> (Setof Atom)
                                 (values (Setof Tag)
                                         (Setof Prod)
                                         (Setof Arrow))))
(define (extract-positive-literals P)
  (let loop : (values (Setof Tag)
                      (Setof Prod)
                      (Setof Arrow))
    ([todo : (Setof Atom) P]
     [Ptag : (Setof Tag) (set)]
     [Pprod : (Setof Prod) (set)]
     [Parrow : (Setof Arrow) (set)])
    (match todo
      [(list) (values Ptag Pprod Parrow)]
      [(cons a as)
       (cond
         [(Tag? a) (loop as (cons a Ptag) Pprod Parrow)]
         [(Prod? a) (loop as Ptag (cons a Pprod) Parrow)]
         [else (loop as Ptag Pprod (cons a Parrow))])])))


(: uninhabitited-Tag-clause?
   (-> (Setof Tag) (Setof (Not Tag)) Boolean))
(define (uninhabitited-Tag-clause? P N)
  (cond
    [(< 1 (set-count (remove-duplicates P)))
     #true]
    [else
     (exists (λ ([n : (Not Tag)]) (set-member? P (Not-t n)))
             N)]))


(: uninhabitited-Prod-clause?
   (-> (Setof Prod) (Setof (Not Prod)) Boolean))
(define (uninhabitited-Prod-clause? P N)
  (let ([s1 (And (map Prod-l P))]
        [s2 (And (map Prod-r P))])
    (forall
     (λ ([N* : (Setof (Not Prod))])
       (or (let ([t1 (Or (map (λ ([p : (Not Prod)])
                                (Prod-l (Not-t p)))
                              N*))])
             (subtype? s1 t1))
           (let* ([N-N* (set-diff N N*)]
                  [t2 (Or (map (λ ([p : (Not Prod)])
                                 (Prod-r (Not-t p)))
                               N-N*))])
             (subtype? s2 t2))))
     (subsets N))))



(: uninhabitited-Arrow-clause?
   (-> (Setof Arrow) (Setof (Not Arrow)) Boolean))
(define (uninhabitited-Arrow-clause? P N)
  (let ([dom (Or (map Arrow-dom P))])
    (exists (λ ([na : (Not Arrow)])
              (let ([t1 (Arrow-dom (Not-t na))]
                    [t2 (Arrow-rng (Not-t na))])
                (and (subtype? t1 dom)
                     (forall (λ ([P* : (Setof Arrow)])
                               (or (let ([s1 (Or (map Arrow-dom P*))])
                                     (subtype? t1 s1))
                                   (let ([s2 (And (map Arrow-rng (set-diff P P*)))])
                                     (subtype? s2 t2))))
                             (strict-subsets P)))))
            N)))

(module+ test
  (run-subtype-tests ->Type subtype?))

;(module+ benchmark
;  (run-subtype-benchmark "naive" subtype?))

