#lang typed/racket/base

(require "set-utils.rkt")

(define-type Atom (U Symbol Range Prod Arrow))
(define-type Type (U Atom Var Rec Or And (Not Type)))

(define-type Bound (U Integer -inf.0 +inf.0))
(struct Range ([lower : Bound] [upper : Bound]) #:transparent)
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

(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (uninhabited? (And (set t1 (Not t2)))))

(: uninhabited? (-> Type Boolean))
(define (uninhabited? t) (error 'todo))


