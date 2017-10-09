#lang typed/racket/base

(require "set-utils.rkt")

(define-type Tag Symbol)

(define-type Atom (U Tag Range Prod Arrow))
(define-type Type (U Atom Var Rec Or And (Not Type)))

(struct Range ([lower : Real] [upper : Real]) #:transparent)
(struct Prod ([l : Type] [r : Type]) #:transparent)
(struct Arrow ([dom : Type] [rng : Type]) #:transparent)
(struct Or ([ts : (Setof Type)]) #:transparent)
(struct And ([ts : (Setof Type)]) #:transparent)
(struct (α) Not ([t : α]) #:transparent)
(struct Var ())
(struct Rec ([x : Var] [t : Atom]) #:transparent)

(define Univ : Type (And (set)))
(define Empty : Type (Not Univ))
(define UnivProd : Type (Prod Univ Univ))
(define UnivArrow : Type (Arrow Empty Univ))
(define Int : Type (Range -inf.0 +inf.0))
(define UnivTag : Type (Not (Or (set UnivProd UnivArrow Int))))


(define-type Literal (U Atom (Not Atom)))


(struct Disjunct ([clauses : (Listof Conjunct)]))

(define-type Conjunct (U TagConjunct
                         RangeConjunct
                         ProdConjunct
                         ArrowConjunct))

(struct TagConjunct ([pos : (Setof Tag)] [neg : (Setof Tag)]))
(struct RangeConjunct ([pos : (Setof Range)] [neg : (Setof Range)]))
(struct ProdConjunct ([pos : (Setof Prod)] [neg : (Setof Prod)]))
(struct ArrowConjunct ([pos : (Setof Arrow)] [neg : (Setof Arrow)]))


(: ->DNF (-> Type Disjunct))
(define (->DNF t) (error 'todo))

(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (uninhabited-disjunct?
   (->DNF (And (set t1 (Not t2))))))

(: uninhabited-disjunct? (-> Disjunct Boolean))
(define (uninhabited-disjunct? d)
  (andmap uninhabitited-conjunct? (Disjunct-clauses d)))


(: uninhabitited-conjunct? (-> Conjunct Boolean))
(define (uninhabitited-conjunct? c)
  (cond
    [(TagConjunct? c)
     (define pos-tags (TagConjunct-pos c))
     (define neg-tags (TagConjunct-pos c))
     (cond
       ;; tags are necessarily disjoint, so if there are 2
       ;; or more this type is uninhabited
       [(> 1 (set-count pos-tags)) #true]
       ;; is there we know P and ¬P, we have a contradiction
       ;; and the type is not inhabited
       [(sets-overlap? pos-tags neg-tags) #true]
       ;; otherwise it's possible this conjunct is inhabited
       [else #false])]
    [(RangeConjunct? c)
     (define pos-ranges (RangeConjunct-pos c))
     (define neg-ranges (RangeConjunct-pos c))
     (define pos (reduce-pos-ranges pos-ranges))
     (uninhabited-range? (reduce-range-with-negs pos neg-ranges))]
    [(ProdConjunct? c)
     (define pos-tags (ProdConjunct-pos c))
     (define neg-tags (ProdConjunct-pos c))
     (error 'todo-ProdConjunct)]
    [(ArrowConjunct? c)
     (define pos-tags (ArrowConjunct-pos c))
     (define neg-tags (ArrowConjunct-pos c))
     (error 'todo-ArrowConjunct)]))

(: reduce-pos-ranges (-> (Setof Range) Range))
(define (reduce-pos-ranges pos-ranges)
  (let-values
      ([(lower upper)
        (for/fold ([lower : Real -inf.0]
                   [upper : Real +inf.0])
                  ([r (in-set pos-ranges)])
          (values (max lower (Range-lower r))
                  (min upper (Range-upper r))))])
    (Range lower upper)))


(: uninhabited-range? (-> Range Boolean))
(define (uninhabited-range? r)
  (define lower (Range-lower r))
  (define upper (Range-upper r))
  (and lower upper (> lower upper)))

(: reduce-range-with-negs (-> Range (Setof Range) Range))
(define (reduce-range-with-negs pos neg-ranges)
  (error 'foo))

(: range-subtract (-> Range Range Range))
(define (range-subtract r1 r2)
  (define lower (Range-lower r1))
  (define upper (Range-upper r1))
  (define neg-lower (Range-lower r2))
  (define neg-upper (Range-upper r2))
  (error 'todo))
