#lang typed/racket/base

(require racket/list
         racket/match
         "set-utils.rkt")

(define-type Tag Symbol)
(define tag? symbol?)

(define-type Atom (U Tag Range Prod Arrow))
(define-predicate Atom? Atom)

(define-type Type (U Atom (Or Type) (And Type) (Not Type)))

(struct Range ([lower : Real] [upper : Real]) #:transparent)
(struct Prod ([l : Type] [r : Type]) #:transparent)
(struct Arrow ([dom : Type] [rng : Type]) #:transparent)
(struct (α) Or ([elems : (Setof α)]) #:transparent)
(struct (α) And ([elems : (Setof α)]) #:transparent)
(struct (α) Not ([body : α]) #:transparent)
;(struct Var ())
;(struct Rec ([x : Var] [t : Atom]) #:transparent)

(define Univ (And (set)))
(define Empty (Or (set)))
(define UnivProd (Prod Univ Univ))
(define UnivArrow (Arrow Empty Univ))
(define Int (Range -inf.0 +inf.0))
(define UnivTag (Not (Or (set UnivProd UnivArrow Int))))

(define-type Literal (U Atom (Not Atom)))
(define-predicate literal? Literal)

(define-type Clause (U Literal (And Literal)))
(define-type DNF (U Clause (Or Clause)))

(: ->DNF (-> Type DNF))
(define (->DNF t)
  (match t
    [(? literal? l) l]
    [(Not (And ts)) (Or-DNF-fold (λ ([t : Type]) (->DNF (Not t))) ts)]
    [(Not (Or ts)) (And-DNF-fold (λ ([t : Type]) (->DNF (Not t))) ts)]
    [(Or ts) (Or-DNF-fold ->DNF ts)]
    [(And ts) (And-DNF-fold ->DNF ts)]))

(: And-DNF-fold (-> (-> Type DNF) (Listof Type) DNF))
(define (And-DNF-fold f ts)
  (let loop ([todo : (Listof Type) ts]
             [ors : (Listof (Or Clause)) '()]
             [result : (Listof Literal) '()])
    (match todo
      [(list)
       (match ors
         [(list) (if (= 1 (length result))
                     (car result)
                     (And result))]
         [(cons (Or or-ts) rst)
          (define and-ts (append rst result))
          (->DNF (Or (map (λ ([t : Type]) (And (set-add and-ts t)))
                          or-ts)))])]
      [(cons (app f t) rst)
       (match t
         [(? literal? l)
          (loop rst ors (set-add result l))]
         [(And ls)
          (loop rst ors (append ls result))]
         [(? Or? d)
          (loop rst (set-add ors d) result)])])))

(: Or-DNF-fold (-> (-> Type DNF) (Listof Type) DNF))
(define (Or-DNF-fold f ts)
  (let loop ([todo : (Listof Type) ts]
             [result : (Listof Clause) '()])
    (match todo
      [(list) (if (= 1 (length result))
                  (first result)
                  (Or result))]
      [(cons (app f d) rst)
       (cond
         [(Or? d) (loop rst (append (Or-elems d) result))]
         [else (loop rst (set-add result d))])])))

(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (uninhabited-DNF?
   (->DNF (And (set t1 (Not t2))))))

(: uninhabited-DNF? (-> DNF Boolean))
(define (uninhabited-DNF? d)
  (error 'TODO))


;(: uninhabitited-tag-conjunct? (-> (Tuple (Setof Tag) (Setof (Not Tag))) Boolean))
;(define (uninhabitited-tag-conjunct? c)
;  (match-define (list pos neg) c)
;  (cond
;    [(> 1 (set-count pos)) #true]
;    [(ormap (λ ([t : (Not Tag)]) (member (Not-t t) pos))
;            neg)
;     #true]
;    [else #false]))
;
;
;(: uninhabitited-range-conjunct? (-> (Tuple (Setof Range) (Setof (Not Range)))
;                                     Boolean))
;(define (uninhabitited-range-conjunct? c)
;  (match-define (list pos neg) c)
;  ;; this should be sound but not complete... oh well
;  (uninhabited-range? (reduce-range-with-negs (combine-ranges pos) neg)))
;
;
;(: uninhabitited-prod-conjunct? (-> (Tuple (Setof Prod) (Setof (Not Prod))) Boolean))
;(define (uninhabitited-prod-conjunct? c)
;  (match-define (list pos neg) c)
;  (andmap (λ ([N* : (Setof (Not Prod))])
;            (or (subtype? (And (map Prod-l pos))
;                          (Or (map (λ ([p : (Not Prod)]) (Prod-l (Not-t p))) neg)))
;                (let ([N*-comp (set-diff neg N*)])
;                  (subtype? (And (map Prod-r pos))
;                            (Or (map (λ ([p : (Not Prod)]) (Prod-r (Not-t p))) N*-comp))))))
;          (powerset neg)))
;
;
;(: uninhabitited-arrow-conjunct? (-> (Tuple (Setof Arrow) (Setof (Not Arrow)))
;                                     Boolean))
;(define (uninhabitited-arrow-conjunct? c)
;  (error 'todo-ArrowConjunct))
;
;
;(: uninhabited-range? (-> Range Boolean))
;;; is a given range uninhabited
;(define (uninhabited-range? r)
;  (match-define (Range lower upper) r)
;  (and lower upper (> lower upper)))
;
;
;(: combine-ranges (-> (Setof Range) Range))
;;; given a bunch of known ranges, collapse them
;;; into a single range
;(define (combine-ranges pos-ranges)
;  (let-values
;      ([(lower upper)
;        (for/fold ([lower : Real -inf.0]
;                   [upper : Real +inf.0])
;                  ([r (in-set pos-ranges)])
;          (values (max lower (Range-lower r))
;                  (min upper (Range-upper r))))])
;    (Range lower upper)))
;
;
;(: reduce-range-with-negs (-> Range (Setof (Not Range)) Range))
;;; a sound but incomplete procedure that reduces some
;;; range (pos) with a but of ranges that the value is known
;;; to not be in. Notably, this function will not "partition"
;;; the range, it only shrinks the range.
;(define (reduce-range-with-negs pos neg-ranges)
;  (define-values (new-lower new-upper)
;    (for/fold : (values Real Real)
;      ([lower (Range-lower pos)]
;       [upper (Range-upper pos)])
;      ([neg (in-set neg-ranges)])
;      (match-define (Not (Range neg-lower neg-upper)) neg)
;      (cond
;        [(or (< neg-upper lower)
;             (> neg-lower upper))
;         (values lower upper)]
;        [(<= neg-lower lower)
;         (cond
;           [(>= neg-upper upper) (values +inf.0 -inf.0)]
;           [else (values (add1 neg-upper) upper)])]
;        [else
;         (cond
;           [(>= neg-upper upper) (values lower (sub1 neg-lower))]
;           [else (values +inf.0 -inf.0)])])))
;  (Range new-lower new-upper))



;(subtype? (Prod Int Int) (Prod Univ Univ))
;(subtype? (Prod Int Int) (Prod Univ Int))
;(subtype? (Prod Int Int) (Prod Int Univ))
;(subtype? (Prod Int Int) (Prod Int Int))
;(subtype? (Prod Int Int) (Prod Empty Int))
;(subtype? (Prod Int Int) (Prod Int Empty))
;(subtype? (Prod Int Int) (Prod Empty Empty))




