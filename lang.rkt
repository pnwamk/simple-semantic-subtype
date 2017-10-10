#lang typed/racket/base

(require racket/list
         racket/match
         "set-utils.rkt")

(define-type Tag Symbol)
(define tag? symbol?)

(define-type Atom (U Tag Range Prod Arrow))
(define-predicate Atom? Atom)

(define-type Type (U Atom Or And (Not Type)))

(struct Range ([lower : Real] [upper : Real]) #:transparent)
(struct Prod ([l : Type] [r : Type]) #:transparent)
(struct Arrow ([dom : Type] [rng : Type]) #:transparent)
(struct Or ([ts : (Setof Type)]) #:transparent)
(struct And ([ts : (Setof Type)]) #:transparent)
(struct (α) Not ([t : α]) #:transparent)
;(struct Var ())
;(struct Rec ([x : Var] [t : Atom]) #:transparent)

(define Univ : Type (And (set)))
(define Empty : Type (Not Univ))
(define UnivProd : Type (Prod Univ Univ))
(define UnivArrow : Type (Arrow Empty Univ))
(define Int : Type (Range -inf.0 +inf.0))
(define UnivTag : Type (Not (Or (set UnivProd UnivArrow Int))))


(struct DNF ([tags   : (Tuple (Setof Tag)   (Setof (Not Tag)))]
             [ranges : (Tuple (Setof Range) (Setof (Not Range)))]
             [products  : (Tuple (Setof Prod)  (Setof (Not Prod)))]
             [arrows : (Tuple (Setof Arrow) (Setof (Not Arrow)))]))

(define empty-clause (list (set) (set)))
(define empty-disj (DNF empty-clause
                        empty-clause
                        empty-clause
                        empty-clause))

(: ->DNF (-> Type DNF))
(define (->DNF t)
  (match t
    [(? tag?)
     (DNF (list (set t) (set))
          empty-clause
          empty-clause
          empty-clause)]
    [(? Range?)
     (DNF empty-clause
          (list (set t) (set))
          empty-clause
          empty-clause)]
    [(? Prod?)
     (DNF empty-clause
          empty-clause
          (list (set t) (set))
          empty-clause)]
    [(? Arrow?)
     (DNF empty-clause
          empty-clause
          empty-clause
          (list (set t) (set)))]
    [(Not (? tag? t))
     (DNF (list (set) (set (Not t)))
          empty-clause
          empty-clause
          empty-clause)]
    [(Not (? Range? t))
     (DNF empty-clause
          (list (set) (set (Not t)))
          empty-clause
          empty-clause)]
    [(Not (? Prod? t))
     (DNF empty-clause
          empty-clause
          (list (set) (set (Not t)))
          empty-clause)]
    [(Not (? Arrow? t))
     (DNF empty-clause
          empty-clause
          empty-clause
          (list (set) (set (Not t))))]
    [(Or ts)
     (foldl disjunct-or
            empty-disj
            (map ->DNF ts))]
    [(And ts)
     (foldl disjunct-and
            empty-disj
            (map ->DNF ts))]))

(: disjunct-or (-> DNF DNF DNF))
(define (disjunct-or d1 d2)
  (match* (d1 d2)
    [((DNF (list ts1+ ts1-)
           (list rs1+ rs1-)
           (list ps1+ ps1-)
           (list as1+ as1-))
      (DNF (list ts2+ ts2-)
           (list rs2+ rs2-)
           (list ps2+ ps2-)
           (list as2+ as2-)))
     (DNF (list (set-union ts1+ ts2+)
                (set-union ts1- ts2-))
          (list (set-union rs1+ rs2+)
                (set-union rs1- rs2-))
          (list (set-union ps1+ ps2+)
                (set-union ps1- ps2-))
          (list (set-union as1+ as2+)
                (set-union as1- as2-)))]))

(: disjunct-and (-> DNF DNF DNF))
(define (disjunct-and d1 d2)
  (match* (d1 d2)
    [((DNF (list ts1+ ts1-)
           (list rs1+ rs1-)
           (list ps1+ ps1-)
           (list as1+ as1-))
      (DNF (list ts2+ ts2-)
           (list rs2+ rs2-)
           (list ps2+ ps2-)
           (list as2+ as2-)))
     (DNF (list (set-union ts1+ ts2+) (set-union ts1- ts2-))
          (list (set-union rs1+ rs2+) (set-union rs1- rs2-))
          (list (set-union ps1+ ps2+) (set-union ps1- ps2-))
          (list (set-union as1+ as2+) (set-union as1- as2-)))]))



(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (uninhabited-disjunct?
   (->DNF (And (set t1 (Not t2))))))

(: uninhabited-disjunct? (-> DNF Boolean))
(define (uninhabited-disjunct? d)
  (and (uninhabitited-tag-conjunct?   (DNF-tags d))
       (uninhabitited-range-conjunct? (DNF-ranges d))
       (uninhabitited-prod-conjunct?  (DNF-products d))
       (uninhabitited-arrow-conjunct? (DNF-arrows d))))


(: uninhabitited-tag-conjunct? (-> (Tuple (Setof Tag) (Setof (Not Tag))) Boolean))
(define (uninhabitited-tag-conjunct? c)
  (match-define (list pos neg) c)
  (cond
    [(> 1 (set-count pos)) #true]
    [(ormap (λ ([t : (Not Tag)]) (member (Not-t t) pos))
            neg)
     #true]
    [else #false]))


(: uninhabitited-range-conjunct? (-> (Tuple (Setof Range) (Setof (Not Range)))
                                     Boolean))
(define (uninhabitited-range-conjunct? c)
  (match-define (list pos neg) c)
  ;; this should be sound but not complete... oh well
  (uninhabited-range? (reduce-range-with-negs (combine-ranges pos) neg)))


(: uninhabitited-prod-conjunct? (-> (Tuple (Setof Prod) (Setof (Not Prod))) Boolean))
(define (uninhabitited-prod-conjunct? c)
  (match-define (list pos neg) c)
  (andmap (λ ([N* : (Setof (Not Prod))])
            (or (subtype? (And (map Prod-l pos))
                          (Or (map (λ ([p : (Not Prod)]) (Prod-l (Not-t p))) neg)))
                (let ([N*-comp (set-diff neg N*)])
                  (subtype? (And (map Prod-r pos))
                            (Or (map (λ ([p : (Not Prod)]) (Prod-r (Not-t p))) N*-comp))))))
          (powerset neg)))


(: uninhabitited-arrow-conjunct? (-> (Tuple (Setof Arrow) (Setof (Not Arrow)))
                                     Boolean))
(define (uninhabitited-arrow-conjunct? c)
  (error 'todo-ArrowConjunct))


(: uninhabited-range? (-> Range Boolean))
;; is a given range uninhabited
(define (uninhabited-range? r)
  (match-define (Range lower upper) r)
  (and lower upper (> lower upper)))


(: combine-ranges (-> (Setof Range) Range))
;; given a bunch of known ranges, collapse them
;; into a single range
(define (combine-ranges pos-ranges)
  (let-values
      ([(lower upper)
        (for/fold ([lower : Real -inf.0]
                   [upper : Real +inf.0])
                  ([r (in-set pos-ranges)])
          (values (max lower (Range-lower r))
                  (min upper (Range-upper r))))])
    (Range lower upper)))


(: reduce-range-with-negs (-> Range (Setof (Not Range)) Range))
;; a sound but incomplete procedure that reduces some
;; range (pos) with a but of ranges that the value is known
;; to not be in. Notably, this function will not "partition"
;; the range, it only shrinks the range.
(define (reduce-range-with-negs pos neg-ranges)
  (define-values (new-lower new-upper)
    (for/fold : (values Real Real)
      ([lower (Range-lower pos)]
       [upper (Range-upper pos)])
      ([neg (in-set neg-ranges)])
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
           [else (values +inf.0 -inf.0)])])))
  (Range new-lower new-upper))



(subtype? (Prod Int Int) (Prod Univ Univ))
(subtype? (Prod Int Int) (Prod Univ Int))
(subtype? (Prod Int Int) (Prod Int Univ))
(subtype? (Prod Int Int) (Prod Int Int))
(subtype? (Prod Int Int) (Prod Empty Int))
(subtype? (Prod Int Int) (Prod Int Empty))
(subtype? (Prod Int Int) (Prod Empty Empty))




