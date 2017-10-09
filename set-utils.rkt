#lang typed/racket/base

(require (for-syntax typed/racket/base))

(provide (all-defined-out))

(define-type (Setof T) (Immutable-HashTable T True))

(: set (All (T) (->* () #:rest T (Setof T))))
(define (set . elems)
  (for/hash : (Setof T) ([elem (in-list elems)])
    (values elem #t)))

(define set-count hash-count)

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

(: sets-overlap? (All (T) (-> (Setof T) (Setof T) Boolean)))
(define (sets-overlap? s1 s2)
  (cond
    [(> (set-count s1) (set-count s2)) (sets-overlap? s2 s1)]
    [else
     (for/or : Boolean ([elem (in-immutable-hash-keys s1)])
       (hash-has-key? s2 elem))]))


(define-syntax in-set (make-rename-transformer #'in-immutable-hash-keys))
