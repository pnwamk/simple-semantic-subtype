#lang typed/racket/base

(require racket/list
         racket/match
         "set-utils.rkt")

(define-syntax def-struct
  (syntax-rules ()
      [(_ name (fld ...))
       (struct name (fld ...) #:transparent)]
    [(_ #:∀ (poly-ids ...) name (fld ...))
       (struct (poly-ids ...) name (fld ...) #:transparent)]))


(define-type Atom (U Tag Range Prod Arrow))
(define-type Type (U Atom (Or Type) (And Type) (Not Type)))
(define-type Literal (U Atom (Not Atom)))
(define-type Clause (U Literal (And Literal)))
(define-type DNF (U Clause (Or Clause)))

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
(define UnivTag (Not (Or (set UnivProd UnivArrow Int))))

(define Tag? symbol?)


(define-predicate Atom? Atom)
(define-predicate Not-Atom? (Not Atom))
(define-predicate Not-Tag? (Not Tag))
(define-predicate Not-Range? (Not Range))
(define-predicate Not-Prod? (Not Prod))
(define-predicate Not-Arrow? (Not Arrow))
(define-predicate literal? Literal)


(: ->DNF (-> Type DNF))
(define (->DNF t)
  (match t
    [(? literal? l) l]
    [(Not (And ts)) (DNF-Or-Map (λ ([t : Type]) (->DNF (Not t))) ts)]
    [(Not (Or ts)) (DNF-And-map (λ ([t : Type]) (->DNF (Not t))) ts)]
    [(Or ts) (DNF-Or-Map ->DNF ts)]
    [(And ts) (DNF-And-map ->DNF ts)]))

(: literal-negate (-> Literal Literal))
(define (literal-negate l)
  (match l
    [(? Atom? a) (Not a)]
    [(Not a) a]))

(: DNF-And-map (-> (-> Type DNF) (Setof Type) DNF))
(define (DNF-And-map f ts)
  (let loop ([todo : (Setof Type) ts]
             [ors : (Setof (Or Clause)) (set)]
             [result : (Setof Literal) (set)])
    (match todo
      [(list)
       (match ors
         [(list) (if (= 1 (set-count result))
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

(: DNF-Or-Map (-> (-> Type DNF) (Setof Type) DNF))
(define (DNF-Or-Map f ts)
  (let loop ([todo : (Setof Type) ts]
             [result : (Setof Clause) (set)])
    (match todo
      [(list) (if (= 1 (set-count result))
                  (first result)
                  (Or result))]
      [(cons (app f d) rst)
       (cond
         [(Or? d) (loop rst (append (Or-ts d) result))]
         [else (loop rst (set-add result d))])])))

(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (uninhabited-DNF?
   (->DNF (And (set t1 (Not t2))))))

#|
(define-type Clause (U Literal (And Literal)))
(define-type DNF (U Clause (Or Clause)))
|#

(: uninhabited-DNF? (-> DNF Boolean))
(define (uninhabited-DNF? d)
  (match d
    [(? literal?) #f]
    [(? And? clause) (uninhabitited-DNF-clause? clause)]
    [(Or cs) (andmap uninhabitited-DNF-clause? cs)]))

(: uninhabitited-DNF-clause? (-> Clause Boolean))
(define (uninhabitited-DNF-clause? clause)
  (match clause
    [(? literal?) #f]
    [(And ls)
     (define pos (filter Atom? ls))
     (define-values (tags+ ranges+ prods+ arrows+)
       (extract-positive-literals pos))
     (cond
       [(non-empty-set? tags+)
        (cond
          [(or (non-empty-set? ranges+)
               (non-empty-set? prods+)
               (non-empty-set? arrows+))
           #t]
          [else
           (uninhabitited-Tag-clause? tags+ (filter Not-Tag? ls))])]
       [(non-empty-set? ranges+)
        (cond
          [(or (non-empty-set? prods+)
               (non-empty-set? arrows+))
           #t]
          [else
           (uninhabitited-Range-clause? ranges+ (filter Not-Range? ls))])]
       [(non-empty-set? prods+)
        (cond
          [(non-empty-set? arrows+) #t]
          [else
           (uninhabitited-Prod-clause? prods+ (filter Not-Prod? ls))])]
       [(non-empty-set? arrows+)
        (uninhabitited-Arrow-clause? arrows+ (filter Not-Arrow? ls))]
       [else #f])]))

(: extract-positive-literals (-> (Setof Atom)
                                 (values (Setof Tag)
                                         (Setof Range)
                                         (Setof Prod)
                                         (Setof Arrow))))
(define (extract-positive-literals pos)
  (let loop : (values (Setof Tag)
                      (Setof Range)
                      (Setof Prod)
                      (Setof Arrow))
    ([todo : (Setof Atom) pos]
     [tags+ : (Setof Tag) (set)]
     [ranges+ : (Setof Range) (set)]
     [prods+ : (Setof Prod) (set)]
     [arrows+ : (Setof Arrow) (set)])
    (match todo
      [(list) (values tags+ ranges+ prods+ arrows+)]
      [(cons a as)
       (cond
         [(Tag? a) (loop as (cons a tags+) ranges+ prods+ arrows+)]
         [(Range? a) (loop as tags+ (cons a ranges+) prods+ arrows+)]
         [(Prod? a) (loop as tags+ ranges+ (cons a prods+) arrows+)]
         [else (loop as tags+ ranges+ prods+ (cons a arrows+))])])))


(: uninhabitited-Tag-clause? (-> (Setof Tag) (Setof (Not Tag)) Boolean))
(define (uninhabitited-Tag-clause? pos neg)
  (cond
    [(check-duplicates pos) #true]
    [else
     (ormap (λ ([n : (Not Tag)]) (set-member? pos (Not-t n)))
            neg)]))

(: uninhabitited-Range-clause? (-> (Setof Range) (Setof (Not Range)) Boolean))
(define (uninhabitited-Range-clause? pos neg)
  (uninhabited-range? (reduce-range-with-negs (combine-ranges pos) neg)))

(: uninhabitited-Prod-clause? (-> (Setof Prod) (Setof (Not Prod)) Boolean))
(define (uninhabitited-Prod-clause? pos neg) (error 'todo))

(: uninhabitited-Arrow-clause? (-> (Setof Arrow) (Setof (Not Arrow)) Boolean))
(define (uninhabitited-Arrow-clause? pos neg) (error 'todo))


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
(: uninhabited-range? (-> Range Boolean))
;; is a given range uninhabited
(define (uninhabited-range? r)
  (match-define (Range lower upper) r)
  (and lower upper (> lower upper)))


(: combine-ranges (-> (Setof Range) Range))
;; given a bunch of known ranges, collapse them
;; into a single range
(define (combine-ranges pos-ranges)
  (let-values
      ([(lower upper)
        (for/fold ([lower : Real -inf.0]
                   [upper : Real +inf.0])
                  ([r (in-set pos-ranges)])
          (values (max lower (Range-lower r))
                  (min upper (Range-upper r))))])
    (Range lower upper)))


(: reduce-range-with-negs (-> Range (Setof (Not Range)) Range))
;; a sound but incomplete procedure that reduces some
;; range (pos) with a but of ranges that the value is known
;; to not be in. Notably, this function will not "partition"
;; the range, it only shrinks the range.
(define (reduce-range-with-negs pos neg-ranges)
  (define-values (new-lower new-upper)
    (for/fold : (values Real Real)
      ([lower (Range-lower pos)]
       [upper (Range-upper pos)])
      ([neg (in-set neg-ranges)])
      (match-define (Not (Range neg-lower neg-upper)) neg)
      (cond
        [(or (< neg-upper lower)
             (> neg-lower upper))
         (values lower upper)]
        [(<= neg-lower lower)
         (cond
           [(>= neg-upper upper) (values +inf.0 -inf.0)]
           [else (values (add1 neg-upper) upper)])]
        [else
         (cond
           [(>= neg-upper upper) (values lower (sub1 neg-lower))]
           [else (values +inf.0 -inf.0)])])))
  (Range new-lower new-upper))



;(subtype? (Prod Int Int) (Prod Univ Univ))
;(subtype? (Prod Int Int) (Prod Univ Int))
;(subtype? (Prod Int Int) (Prod Int Univ))
;(subtype? (Prod Int Int) (Prod Int Int))
;(subtype? (Prod Int Int) (Prod Empty Int))
;(subtype? (Prod Int Int) (Prod Int Empty))
;(subtype? (Prod Int Int) (Prod Empty Empty))




