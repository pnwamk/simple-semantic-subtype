#lang typed/racket/base

(require racket/match
         racket/set
         "grammar.rkt")

(provide (all-defined-out))

(define-syntax def-struct
  (syntax-rules ()
      [(_ name (fld ...))
       (struct name (fld ...) #:transparent)]
    [(_ #:∀ (poly-ids ...) name (fld ...))
       (struct (poly-ids ...) name (fld ...) #:transparent)]))


(define-type Atom (U Tag Prod Arrow))
(define-type Type (U Atom Or Univ))

(define-type Tag Symbol)
(def-struct Prod ([l : Type]
                  [r : Type]))
(def-struct Arrow ([dom : Type]
                   [rng : Type]))
(def-struct Or ([ts : (Setof Type)]))
(def-struct Univ ())

(: -or (-> Type * Type))
(define (-or . initial-ts)
  (let loop ([todo   : (Listof Type) initial-ts]
             [result : (Listof Type) '()])
    (match todo
      [(cons (Or ts*) ts)
       (loop ts (append (set->list ts*) result))]
      [(cons (? Univ?) ts) (Univ)]
      [(cons t ts)
       (loop ts (cons t result))]
      [_ (Or (list->set result))])))


;(struct Var ())
;(struct Rec ([x : Var] [t : Atom]) #:transparent)

(define Empty (Or (set)))

(define UnivProd (Prod (Univ) (Univ)))
(define UnivArrow (Arrow Empty (Univ)))

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




(define Bool (-or T F))
(define Tag? symbol?)


(define-predicate Atom? Atom)


(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (match* (t1 t2)
    [(_ _) #:when (equal? t1 t2) #t]
    [(_ (? Univ?)) #t]
    [((Or ts) t2)
     (for/and : Boolean ([t (in-set ts)])
       (subtype? t t2))]
    [(t1 (Or ts))
     (or (set-member? ts t1)
         (for/or : Boolean ([t (in-set ts)])
           (subtype? t1 t)))]
    [((Prod t1 t2) (Prod s1 s2))
     (and (subtype? t1 s1)
          (subtype? t2 s2))]
    [((Arrow t1 t2) (Arrow s1 s2))
     (and (subtype? s1 t1)
          (subtype? t2 s2))]
    [(_ _) #f]))



(: ->Type (-> TypeSexp Type))
(define (->Type sexp)
  (match sexp
    ['Univ (Univ)]
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
    [`(Or . ,ts) (apply -or (map ->Type ts))]))

;|#
