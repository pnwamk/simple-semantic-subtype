#lang typed/racket/base

(require racket/list
         (for-syntax typed/racket/base))

(provide (all-defined-out))

(define-type TagSet (Immutable-HashTable Fixnum True))

(: set (-> Fixnum * TagSet))
(define set
  (case-lambda
    [() (hasheq)]
    [elems (for/hasheq : TagSet
             ([elem (in-list elems)])
             (values elem #t))]))


(define set-count length)
(define set-empty? null?)

(: non-empty-set? (-> (Setof Any) Boolean))
(define non-empty-set? pair?)

(: set-add (-> TagSet Fixnum TagSet))
(define (set-add s elem)
  (hash-set s elem #t))

(: set-remove (-> TagSet Fixnum TagSet))
(define (set-remove s elem)
  (hash-remove s elem))

(: set-member? (All (T) (-> TagSet T Boolean)))
(define (set-member? s elem)
  (hash-ref s elem #f))

(: set-union (-> TagSet TagSet TagSet))
(define (set-union s1 s2)
  (: union (-> TagSet TagSet TagSet))
  (define (union s1 s2)
    (for/fold ([s : TagSet s1])
              ([elem : Fixnum (in-immutable-hash-keys s2)])
      (hash-set s elem #t)))
  (if (> (hash-count s1)
         (hash-count s2))
      (union s1 s2)
      (union s2 s1)))

(: set-diff (-> TagSet TagSet TagSet))
(define (set-diff s other)
  (for/fold ([s : TagSet s])
            ([elem : Fixnum (in-immutable-hash-keys other)])
    (hash-remove s elem)))


(define-syntax in-tag-set (make-rename-transformer #'in-immutable-hash-keys))
