#lang typed/racket/base

(provide (all-defined-out))

(define-type (Setof T) (Immutable-HashTable T True))

(: set (All (T) (->* () #:rest T (Setof T))))
(define (set . elems)
  (for/hash : (Setof T) ([elem (in-list elems)])
    (values elem #t)))

(: set-add (All (T) (-> (Setof T) T (Setof T))))
(define (set-add s elem)
  (hash-set s elem #t))

(: set-remove (All (T) (-> (Setof T) T (Setof T))))
(define (set-remove s elem)
  (hash-remove s elem))

(: set-member? (All (T) (-> (Setof T) T Boolean)))
(define (set-member? s elem)
  (hash-ref s elem #f))

(: set-union (All (T) (-> (Setof T) (Setof T) (Setof T))))
(define (set-union s others)
  (for/fold ([s : (Setof T) s])
            ([elem (in-immutable-hash-keys others)])
    (hash-set s elem #t)))

(: set-diff (All (T) (-> (Setof T) (Setof T) (Setof T))))
(define (set-diff s others)
  (for/fold ([s : (Setof T) s])
            ([elem (in-immutable-hash-keys others)])
    (hash-remove s elem)))
