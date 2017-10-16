#lang typed/racket/base

(require "set-utils.rkt")

(provide (all-defined-out))

(define-syntax def-struct
  (syntax-rules ()
      [(_ name (fld ...))
       (struct name (fld ...) #:transparent)]
    [(_ #:∀ (poly-ids ...) name (fld ...))
       (struct (poly-ids ...) name (fld ...) #:transparent)]))


(define-type Atom (U Tag Range Prod Arrow))
(define-type Type (U Atom (Or Type) (And Type) (Not Type)))

(define-type Tag Symbol)
(def-struct Range ([lower : Real]
                   [upper : Real]))
(def-struct Prod ([l : Type]
                  [r : Type]))
(def-struct Arrow ([dom : Type]
                   [rng : Type]))
(def-struct #:∀ (α) Or ([ts : (Setof α)]))
(def-struct #:∀ (α) And ([ts : (Setof α)]))
(def-struct #:∀ (α) Not ([t : α]))

;(struct Var ())
;(struct Rec ([x : Var] [t : Atom]) #:transparent)

(define Univ (And (set)))
(define Empty (Or (set)))
(define UnivProd (Prod Univ Univ))
(define UnivArrow (Arrow Empty Univ))
(define Int (Range -inf.0 +inf.0))
(define Nat (Range 0 +inf.0))
(define PosInt (Range 1 +inf.0))
(define NegInt (Range -inf.0 -1))
(define UInt8 (Range 0 255))
(define UInt16 (Range 0 65535))
(define UInt32 (Range 0 4294967295))
(define Int8 (Range -128 127))
(define Int16 (Range -32768 32767))
(define Int32 (Range -2147483648 2147483647))


(define UnivTag (Not (Or (set UnivProd UnivArrow Int))))

(define Bool (Or (set 'True 'False)))
(define Unit 'Unit)

(define Tag? symbol?)


(define-predicate Atom? Atom)
(define-predicate Not-Atom? (Not Atom))
(define-predicate Not-Tag? (Not Tag))
(define-predicate Not-Range? (Not Range))
(define-predicate Not-Prod? (Not Prod))
(define-predicate Not-Arrow? (Not Arrow))

(: Diff (-> Type Type Type))
(define (Diff t1 t2) (And (set t1 (Not t2))))
