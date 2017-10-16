#lang typed/racket/base

(require racket/list
         racket/match
         "base-lang.rkt"
         "set-utils.rkt"
         "tunit.rkt"
         "subtype-test-suite.rkt")


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
  (uninhabited-DNF?
               (->DNF (And (set t1 (Not t2))))))

(: uninhabited-DNF? (-> DNF Boolean))
(define (uninhabited-DNF? d)
  (match d
    [(? Literal?) #false]
    [(? And? clause) (uninhabitited-DNF-clause? clause)]
    [(Or cs) (forall uninhabitited-DNF-clause? cs)]))

(: uninhabitited-DNF-clause? (-> Clause Boolean))
(define (uninhabitited-DNF-clause? clause)
  (match clause
    [(? Literal?) #false]
    [(And ls)
     (define P (filter Atom? ls))
     (define-values (Ptag Prange Pprod Parrow)
       (extract-positive-literals P))
     (cond
       [(non-empty-set? Ptag)
        (cond
          [(or (non-empty-set? Prange)
               (non-empty-set? Pprod)
               (non-empty-set? Parrow))
           #t]
          [else
           (uninhabitited-Tag-clause? Ptag (filter Not-Tag? ls))])]
       [(non-empty-set? Prange)
        (cond
          [(or (non-empty-set? Pprod)
               (non-empty-set? Parrow))
           #t]
          [else
           (uninhabitited-Range-clause? Prange (filter Not-Range? ls))])]
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
                                         (Setof Range)
                                         (Setof Prod)
                                         (Setof Arrow))))
(define (extract-positive-literals P)
  (let loop : (values (Setof Tag)
                      (Setof Range)
                      (Setof Prod)
                      (Setof Arrow))
    ([todo : (Setof Atom) P]
     [Ptag : (Setof Tag) (set)]
     [Prange : (Setof Range) (set)]
     [Pprod : (Setof Prod) (set)]
     [Parrow : (Setof Arrow) (set)])
    (match todo
      [(list) (values Ptag Prange Pprod Parrow)]
      [(cons a as)
       (cond
         [(Tag? a) (loop as (cons a Ptag) Prange Pprod Parrow)]
         [(Range? a) (loop as Ptag (cons a Prange) Pprod Parrow)]
         [(Prod? a) (loop as Ptag Prange (cons a Pprod) Parrow)]
         [else (loop as Ptag Prange Pprod (cons a Parrow))])])))


(: uninhabitited-Tag-clause?
   (-> (Setof Tag) (Setof (Not Tag)) Boolean))
(define (uninhabitited-Tag-clause? P N)
  (cond
    [(< 1 (set-count (remove-duplicates P)))
     #true]
    [else
     (exists (λ ([n : (Not Tag)]) (set-member? P (Not-t n)))
             N)]))

(: uninhabitited-Range-clause?
   (-> (Setof Range) (Setof (Not Range)) Boolean))
(define (uninhabitited-Range-clause? pos neg)
  (uninhabited-range?
   (reduce-range-with-negs
    (combine-ranges pos)
    neg)))


(: uninhabited-range? (-> Range Boolean))
;; is a given range uninhabited
(define (uninhabited-range? r)
  (match-define (Range lower upper) r)
  (and lower upper (> lower upper)))


(: combine-ranges (-> (Setof Range) Range))
;; given a bunch of known ranges, collapse them
;; into a single range
(define (combine-ranges P)
  (let-values
      ([(lower upper)
        (for/fold ([lower : Real -inf.0]
                   [upper : Real +inf.0])
                  ([r (in-set P)])
          (values (max lower (Range-lower r))
                  (min upper (Range-upper r))))])
    (Range lower upper)))


(: reduce-range-with-negs (-> Range (Setof (Not Range)) Range))
;; a sound but incomplete procedure that reduces some
;; range (pos) with a but of ranges that the value is known
;; to not be in. Notably, this function will not "partition"
;; the range, it only shrinks the range.
(define (reduce-range-with-negs r N)
  (define-values (new-lower new-upper)
    (for/fold : (values Real Real)
      ([lower (Range-lower r)]
       [upper (Range-upper r)])
      ([neg (in-set N)])
      (match-define (Not (Range neg-lower neg-upper)) neg)
      (cond
        [(or (< neg-upper lower)
             (> neg-lower upper))
         (values lower upper)]
        [(<= neg-lower lower)
         (cond
           [(>= neg-upper upper) (values +inf.0 -inf.0)]
           [else (values (add1 neg-upper) upper)])]
        [else
         (cond
           [(>= neg-upper upper) (values lower (sub1 neg-lower))]
           ;; in this last case, it would be more complete to reason about
           ;; dividing the range into two ranges (i.e. excluding neg), but
           ;; currently we just leave it unchanged as this is sound (TODO
           ;; make also complete -- i.e. keep track of the list of ranges
           ;; and then at the end check if all are uninhabited)
           [else (values lower upper)])])))
  (Range new-lower new-upper))



(: uninhabitited-Prod-clause?
   (-> (Setof Prod) (Setof (Not Prod)) Boolean))
(define (uninhabitited-Prod-clause? P N)
  (let ([s1 (And (map Prod-l P))]
        [s2 (And (map Prod-r P))])
    (or (subtype? s1 Empty)
        (subtype? s2 Empty)
        (Prod-Phi s1 s2 N))))

(: Prod-Phi (-> Type Type (Setof (Not Prod)) Boolean))
(define (Prod-Phi s1 s2 N)
  (match N
    [(cons (Not (Prod t1 t2)) N)
     (and (or (subtype? s1 t1)
              (Prod-Phi (Diff s1 t1) s2 N))
          (or (subtype? s2 t2)
              (Prod-Phi s1 (Diff s2 t2) N)))]
    [_ #f]))

(: uninhabitited-Arrow-clause?
   (-> (Setof Arrow) (Setof (Not Arrow)) Boolean))
(define (uninhabitited-Arrow-clause? P N)
  (let ([dom (Or (map Arrow-dom P))])
    (exists (λ ([na : (Not Arrow)])
              (let ([t1 (Arrow-dom (Not-t na))]
                    [t2 (Arrow-rng (Not-t na))])
                (and (subtype? t1 dom)
                     (Arrow-Phi t1 (Not t2) P))))
            N)))

(: Arrow-Phi (-> Type Type (Setof Arrow)
                 Boolean))
(define (Arrow-Phi t1 t2 P)
  (match P
    [(cons (Arrow s1* s2*) P)
     (and (or (subtype? t1 s1*)
              (let ([s2 (And (map Arrow-rng P))])
                (subtype? s2 (Not t2))))
          (Arrow-Phi t1 (And (set t2 s2*)) P)
          (Arrow-Phi (Diff t1 s1*) t2 P))]
    [_ #t]))

(module+ test
  (check-false (subtype? (Arrow Int Univ) (Arrow Int Int)))
  ;(run-subtype-tests subtype?)
  )

(module+ benchmark
  (run-subtype-benchmark "naive" subtype?))

