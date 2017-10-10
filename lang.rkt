#lang typed/racket/base

(require racket/match
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


(struct TagConjunct ([pos : (Setof Tag)] [neg : (Setof (Not Tag))]))
(struct RangeConjunct ([pos : (Setof Range)] [neg : (Setof (Not Range))]))
(struct ProdConjunct ([pos : (Setof Prod)] [neg : (Setof (Not Prod))]))
(struct ArrowConjunct ([pos : (Setof Arrow)] [neg : (Setof (Not Arrow))]))

(struct Disjunct ([tag-clauses : TagConjunct]
                  [range-clauses : RangeConjunct]
                  [prod-clauses : ProdConjunct]
                  [arrow-clauses : ArrowConjunct]))

(define empty-disj (Disjunct (TagConjunct   (set) (set))
                             (RangeConjunct (set) (set))
                             (ProdConjunct  (set) (set))
                             (ArrowConjunct (set) (set))))

(: ->DNF (-> Type Disjunct))
(define (->DNF t)
  (match t
    [(? tag?)
     (Disjunct (TagConjunct   (set t) (set))
               (RangeConjunct (set)   (set))
               (ProdConjunct  (set)   (set))
               (ArrowConjunct (set)   (set)))]
    [(? Range?)
     (Disjunct (TagConjunct   (set)   (set))
               (RangeConjunct (set t) (set))
               (ProdConjunct  (set)   (set))
               (ArrowConjunct (set)   (set)))]
    [(? Prod?)
     (Disjunct (TagConjunct   (set)   (set))
               (RangeConjunct (set)   (set))
               (ProdConjunct  (set t) (set))
               (ArrowConjunct (set)   (set)))]
    [(? Arrow?)
     (Disjunct (TagConjunct   (set)   (set))
               (RangeConjunct (set)   (set))
               (ProdConjunct  (set)   (set))
               (ArrowConjunct (set t) (set)))]
    [(Not (? tag? t))
     (Disjunct (TagConjunct   (set) (set (Not t)))
               (RangeConjunct (set) (set))
               (ProdConjunct  (set) (set))
               (ArrowConjunct (set) (set)))]
    [(Not (? Range? t))
     (Disjunct (TagConjunct   (set) (set))
               (RangeConjunct (set) (set (Not t)))
               (ProdConjunct  (set) (set))
               (ArrowConjunct (set) (set)))]
    [(Not (? Prod? t))
     (Disjunct (TagConjunct   (set) (set))
               (RangeConjunct (set) (set))
               (ProdConjunct  (set) (set (Not t)))
               (ArrowConjunct (set) (set)))]
    [(Not (? Arrow? t))
     (Disjunct (TagConjunct   (set) (set))
               (RangeConjunct (set) (set))
               (ProdConjunct  (set) (set))
               (ArrowConjunct (set) (set (Not t))))]
    [(Or ts)
     (foldl disjunct-or
            empty-disj
            (map ->DNF ts))]
    [(And ts)
     (foldl disjunct-and
            empty-disj
            (map ->DNF ts))]))

(: disjunct-or (-> Disjunct Disjunct Disjunct))
(define (disjunct-or d1 d2)
  (match* (d1 d2)
    [((Disjunct (TagConjunct   ts1+ ts1-)
                (RangeConjunct rs1+ rs1-)
                (ProdConjunct  ps1+ ps1-)
                (ArrowConjunct as1+ as1-))
      (Disjunct (TagConjunct   ts2+ ts2-)
                (RangeConjunct rs2+ rs2-)
                (ProdConjunct  ps2+ ps2-)
                (ArrowConjunct as2+ as2-)))
     (Disjunct (TagConjunct   (set-union ts1+ ts2+)
                              (set-union ts1- ts2-))
               (RangeConjunct (set-union rs1+ rs2+)
                              (set-union rs1- rs2-))
               (ProdConjunct  (set-union ps1+ ps2+)
                              (set-union ps1- ps2-))
               (ArrowConjunct (set-union as1+ as2+)
                              (set-union as1- as2-)))]))

(: disjunct-and (-> Disjunct Disjunct Disjunct))
(define (disjunct-and d1 d2)
  (match* (d1 d2)
    [((Disjunct (TagConjunct   ts1+ ts1-)
                (RangeConjunct rs1+ rs1-)
                (ProdConjunct  ps1+ ps1-)
                (ArrowConjunct as1+ as1-))
      (Disjunct (TagConjunct   ts2+ ts2-)
                (RangeConjunct rs2+ rs2-)
                (ProdConjunct  ps2+ ps2-)
                (ArrowConjunct as2+ as2-)))
     (Disjunct (TagConjunct   (set-union ts1+ ts2+) (set-union ts1- ts2-))
               (RangeConjunct (set-union rs1+ rs2+) (set-union rs1- rs2-))
               (ProdConjunct  (set-union ps1+ ps2+) (set-union ps1- ps2-))
               (ArrowConjunct (set-union as1+ as2+) (set-union as1- as2-)))]))



(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (uninhabited-disjunct?
   (->DNF (And (set t1 (Not t2))))))

(: uninhabited-disjunct? (-> Disjunct Boolean))
(define (uninhabited-disjunct? d)
  (and (uninhabitited-tag-conjunct? (Disjunct-tag-clauses d))
       (uninhabitited-range-conjunct? (Disjunct-range-clauses d))
       (uninhabitited-prod-conjunct? (Disjunct-prod-clauses d))
       (uninhabitited-arrow-conjunct? (Disjunct-arrow-clauses d))))


(: uninhabitited-tag-conjunct? (-> TagConjunct Boolean))
(define (uninhabitited-tag-conjunct? c)
  (match-define (TagConjunct pos neg) c)
  (cond
    [(> 1 (set-count pos)) #true]
    [(ormap (λ ([t : (Not Tag)]) (member (Not-t t) pos))
            neg)
     #true]
    [else #false]))


(: uninhabitited-range-conjunct? (-> RangeConjunct Boolean))
(define (uninhabitited-range-conjunct? c)
  (match-define (RangeConjunct pos neg) c)
  ;; this should be sound but not complete... oh well
  (uninhabited-range? (reduce-range-with-negs (combine-ranges pos) neg)))


(: uninhabitited-prod-conjunct? (-> ProdConjunct Boolean))
(define (uninhabitited-prod-conjunct? c)
  (match-define (ProdConjunct pos neg) c)
  (andmap (λ ([N* : (Setof (Not Prod))])
            (or (subtype? (And (map Prod-l pos))
                          (Or (map (λ ([p : (Not Prod)]) (Prod-l (Not-t p))) neg)))
                (let ([N*-comp (set-diff neg N*)])
                  (subtype? (And (map Prod-r pos))
                            (Or (map (λ ([p : (Not Prod)]) (Prod-r (Not-t p))) N*-comp))))))
          (powerset neg)))


(: uninhabitited-arrow-conjunct? (-> ArrowConjunct Boolean))
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




