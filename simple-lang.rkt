#lang typed/racket/base

(require racket/match
         "grammar.rkt"
         "set-utils.rkt")

(provide (all-defined-out))

(define-syntax def-struct
  (syntax-rules ()
      [(_ name (fld ...))
       (struct name (fld ...) #:transparent)]
    [(_ #:∀ (poly-ids ...) name (fld ...))
       (struct (poly-ids ...) name (fld ...) #:transparent)]))


(define-type Atom (U Tag Prod Arrow))
(define-type Type (U Atom (Or Type) (And Type) (Not Type)))

(define-type Tag Symbol)
(def-struct Prod ([l : Type]
                  [r : Type]))
(def-struct Arrow ([dom : Type]
                   [rng : Type]))
(def-struct #:∀ (α) Or ([ts : (Setof α)]))
(def-struct #:∀ (α) And ([ts : (Setof α)]))
(def-struct #:∀ (α) Not ([t : α]))

(: -or (All (X) (-> (∩ Type X) * (Or X))))
(define (-or . ts)
  (Or ts))

(: -and (-> Type * Type))
(define (-and . ts)
  (And ts))

(define -not Not)

;(struct Var ())
;(struct Rec ([x : Var] [t : Atom]) #:transparent)

(define Univ (And (set)))
(define Empty (Or (set)))

(define UnivProd (Prod Univ Univ))
(define UnivArrow (Arrow Empty Univ))

;; 4 bits for non-numeric base types
(define Unit 'Unit)
(define Str 'Str)
(define T 'T)
(define F 'F)

;; bit 5 and greater for disjoint numeric types
(define NegInt<Int32-bits 'NegInt<Int32-bits)
(define Int32<Int16-bits 'Int32<Int16-bits)
(define Int16<Int8-bits 'Int16<Int8-bits)
(define Int8<Zero-bits 'Int8<Zero-bits)
(define Zero-bits 'Zero-bits)
(define Int8>Zero-bits 'Int8>Zero-bits)
(define UInt8>Int8-bits 'UInt8>Int8-bits)
(define Int16>UInt8-bits 'Int16>UInt8-bits)
(define UInt16>Int16-bits 'UInt16>Int16-bits)
(define Int32>UInt16-bits 'Int32>UInt16-bits)
(define UInt32>Int32-bits 'UInt32>Int32-bits)
(define PosInt>UInt32-bits 'PosInt>UInt32-bits)
;; now to define the numeric bases
;; that use those bits

(define UInt8
  (-or Zero-bits
       Int8>Zero-bits
       UInt8>Int8-bits))
(define Int8
  (-or Int8<Zero-bits
       Zero-bits
       Int8>Zero-bits))
(define UInt16
  (-or Zero-bits
       Int8>Zero-bits
       UInt8>Int8-bits
       Int16>UInt8-bits
       UInt16>Int16-bits))
(define Int16
  (-or Int16<Int8-bits
       Int8<Zero-bits
       Zero-bits
       Int8>Zero-bits
       UInt8>Int8-bits
       Int16>UInt8-bits))
(define UInt32
  (-or Zero-bits
       Int8>Zero-bits
       UInt8>Int8-bits
       Int16>UInt8-bits
       UInt16>Int16-bits
       Int32>UInt16-bits
       UInt32>Int32-bits))
(define Int32
  (-or Int32<Int16-bits
       Int16<Int8-bits
       Int8<Zero-bits
       Zero-bits
       Int8>Zero-bits
       UInt8>Int8-bits
       Int16>UInt8-bits
       UInt16>Int16-bits
       Int32>UInt16-bits
       UInt32>Int32-bits))

(define PosInt
  (-or Int8>Zero-bits
       UInt8>Int8-bits
       Int16>UInt8-bits
       UInt16>Int16-bits
       Int32>UInt16-bits
       PosInt>UInt32-bits))

(define Nat
  (-or Zero-bits
       Int8>Zero-bits
       UInt8>Int8-bits
       Int16>UInt8-bits
       UInt16>Int16-bits
       Int32>UInt16-bits
       PosInt>UInt32-bits))

(define NegInt
  (-or NegInt<Int32-bits
       Int32<Int16-bits
       Int16<Int8-bits
       Int8<Zero-bits))

(define Int
  (-or NegInt<Int32-bits
       Int32<Int16-bits
       Int16<Int8-bits
       Int8<Zero-bits
       Zero-bits
       Int8>Zero-bits
       UInt8>Int8-bits
       Int16>UInt8-bits
       UInt16>Int16-bits
       Int32>UInt16-bits
       PosInt>UInt32-bits))


(define UnivTag (Not (-or UnivProd UnivArrow Int)))

(define Bool (-or T F))
(define Tag? symbol?)


(define-predicate Atom? Atom)
(define-predicate Not-Atom? (Not Atom))
(define-predicate Not-Tag? (Not Tag))
(define-predicate Not-Prod? (Not Prod))
(define-predicate Not-Arrow? (Not Arrow))

(: Diff (-> Type Type Type))
(define (Diff t1 t2) (-and t1 (Not t2)))


(: ->Type (-> TypeSexp Type))
(define (->Type sexp)
  (match sexp
    ['Univ Univ]
    ['Empty Empty]
    ['Unit Unit]
    ['Bool Bool]
    ['Str Str]
    ['UnivProd UnivProd]
    ['UnivArrow UnivArrow]
    ['Int Int]
    ['T T]
    ['F F]
    ['Nat Nat]
    ['PosInt PosInt]
    ['NegInt NegInt]
    ['UInt8 UInt8]
    ['UInt16 UInt16]
    ['UInt32 UInt32]
    ['Int8 Int8]
    ['Int16 Int16]
    ['Int32 Int32]
    [`(Prod ,l ,r) (Prod (->Type l) (->Type r))]
    [`(Arrow ,dom ,rng) (Arrow (->Type dom) (->Type rng))]
    [`(Or . ,ts) (Or (map ->Type ts))]
    [`(And . ,ts) (And (map ->Type ts))]
    [`(Not ,t) (Not (->Type t))]))

;|#
