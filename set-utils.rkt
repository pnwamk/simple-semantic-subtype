#lang typed/racket/base

(require racket/list
         (for-syntax typed/racket/base))

(provide (all-defined-out))

(define-type (Setof T) (Listof T))

(: set (All (T) (->* () #:rest T (Setof T))))
(define (set . elems)
  elems)

(define set-count length)

(: set-add (All (T) (-> (Setof T) T (Setof T))))
(define (set-add s elem)
  (cond
    [(member elem s) s]
    [else (cons elem s)]))

(: set-remove (All (T) (-> (Setof T) T (Setof T))))
(define (set-remove s elem)
  (remove elem s))

(: set-member? (All (T) (-> (Setof T) T Boolean)))
(define (set-member? s elem)
  (and (member elem s) #t))

(: set-union (All (T) (-> (Setof T) (Setof T) * (Setof T))))
(define (set-union s . others)
  (remove-duplicates (apply append s others)))

(: set-diff (All (T) (-> (Setof T) (Setof T) (Setof T))))
(define (set-diff s others)
  (remove* others s))

(: sets-overlap? (All (T) (-> (Setof T) (Setof T) Boolean)))
(define (sets-overlap? s1 s2)
  (and (ormap (λ (elem1) (member elem1 s2)) s1) #t))

(: powerset (All (T) (-> (Setof T) (Setof (Setof T)))))
(define (powerset s)
  (cond
    [(pair? s)
     (define x (car s))
     (define psets (powerset (cdr s)))
     (append psets (map (λ ([pset : (Setof T)]) (cons x pset))
                        psets))]
    [else (list s)]))


(define-syntax in-set (make-rename-transformer #'in-list))
