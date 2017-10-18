#lang typed/racket/base

(require racket/match
         (only-in racket/unsafe/ops unsafe-fx<)
         "grammar.rkt")

(provide (all-defined-out))

(define-syntax def-struct
  (syntax-rules ()
      [(_ name (fld ...))
       (struct name (fld ...) #:transparent)]
    [(_ #:∀ (poly-ids ...) name (fld ...))
       (struct (poly-ids ...) name (fld ...) #:transparent)]))


(def-struct Tag ([id : Fixnum]))
(def-struct Range ([lower : Real]
                   [upper : Real]))
(def-struct Prod ([l : BDD]
                  [r : BDD]))
(def-struct Arrow ([dom : BDD]
                   [rng : BDD]))

(define-type Atom (U Tag Range Prod Arrow))

; interp: (Node a l u r) == if a then (l or u) else (r or u)
(def-struct Node ([atom : Atom]
                  [lchild : BDD]
                  [union : BDD]
                  [rchild : BDD]))

(define top 'Top)
(define bot 'Bot)
(define-type Top 'Top)
(define-predicate Top? Top)
(define-type Bot 'Bot)
(define-predicate Bot? Bot)

(define-type BDD (U Top Bot Node))



;(struct Var ())
;(struct Rec ([x : Var] [t : Atom]) #:transparent)


(define UnivProd (Prod top top))
(define UnivArrow (Arrow bot top))
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



(define-predicate Atom? Atom)

(: Atom<? (-> Atom Atom Boolean))
(define (Atom<? a1 a2)
  (match a1
    [(Tag n1) (match a2
                [(Tag n2) (unsafe-fx< n1 n2)]
                [_ #t])]
    [(Range l1 u1) (match a2
                     [(? Tag?) #f]
                     [(Range l2 u2)
                      (cond
                        [(< l1 l2) #t]
                        [(> l1 l2) #f]
                        [(< u1 u2) #t]
                        [else #f])]
                     [_ #t])]
    [(Prod l1 r1) (match a2
                    [(? Tag?) #f]
                    [(? Range?) #f]
                    [(Prod l2 r2)
                     (cond
                       [(BDD<? l1 l2) #t]
                       [(BDD<? l2 l1) #f]
                       [(BDD<? r1 r2) #t]
                       [else #f])]
                    [_ #t])]
    [(Arrow d1 r1) (match a2
                     [(Arrow d2 r2)
                      (cond
                        [(BDD<? d1 d2) #t]
                        [(BDD<? d2 d1) #f]
                        [(BDD<? r1 r2) #t]
                        [else #f])]
                     [_ #f])]))

(: BDD<? (-> BDD BDD Boolean))
(define (BDD<? b1 b2)
  (match b1
    [(? Top?) (not (Top? b2))]
    [(? Bot?) (Node? b2)]
    [(Node a1 l1 u1 r1) (match b2
                          [(Node a2 l2 u2 r2)
                           (cond
                             [(Atom<? a1 a2) #t]
                             [(Atom<? a2 a1) #f]
                             [(BDD<? l1 l2) #t]
                             [(BDD<? l2 l1) #f]
                             [(BDD<? u1 u2) #t]
                             [(BDD<? u2 u1) #f]
                             [(BDD<? r1 r2) #t]
                             [else #f])]
                          [_ #f])]))


(: -atom (-> Atom BDD))
(define (-atom t) (Node t top bot bot))

(: -and (-> BDD BDD BDD))
(define (-and b1 b2)
  (match* (b1 b2)
    [((? Top?) b) b]
    [(b (? Top?)) b]
    [((? Bot?) _) bot]
    [(_ (? Bot?)) bot]
    [((Node a1 _ _ _) (Node a2 _ _ _))
     (cond
       [(Atom<? a1 a2)
        (match-define (Node _ l1 u1 r1) b1)
        (Node a1 (-and l1 b2) (-and u1 b2) (-and r1 b2))]
       [(Atom<? a2 a1)
        (match-define (Node _ l2 u2 r2) b2)
        (Node a2 (-and b1 l2) (-and b1 u2) (-and b1 r2))]
       [else
        (match-define (Node _ l1 u1 r1) b1)
        (match-define (Node _ l2 u2 r2) b2)
        (Node a1
              (-and (-or l1 u1) (-or l2 u2))
              bot
              (-and (-or r1 u1) (-or r2 u2)))])]))

(: -or (-> BDD BDD BDD))
(define (-or b1 b2)
  (match* (b1 b2)
    [((? Top?) _) top]
    [(_ (? Top?)) top]
    [((? Bot?) b) b]
    [(b (? Bot?)) b]
    [((Node a1 _ _ _) (Node a2 _ _ _))
     (cond
       [(Atom<? a1 a2)
        (match-define (Node _ l1 u1 r1) b1)
        (Node a1 l1 (-or u1 b2) r1)]
       [(Atom<? a2 a1)
        (match-define (Node _ l2 u2 r2) b2)
        (Node a2 l2 (-or b1 u2) r2)]
       [else
        (match-define (Node _ l1 u1 r1) b1)
        (match-define (Node _ l2 u2 r2) b2)
        (Node a1 (-or l1 l2) (-or u1 u2) (-or r1 r2))])]))

(: -not (-> BDD BDD))
(define (-not b) (-diff top b))

(: -diff (-> BDD BDD BDD))
(define (-diff b1 b2)
  (error 'TODO)
  #;(match* (b1 b2)
    [(_ (? Top?)) bot]
    [((? Bot?) _) bot]
    [(b (? Bot?)) b]
    [((? Top?) (Node a l r))
     (Node a (-diff top l) (-diff top r))]
    [((Node a1 _ _) (Node a2 _ _))
     (cond
       [(Atom<? a1 a2)
        (match-define (Node _ l1 r1) b1)
        (Node a1 (-diff l1 b2) (-diff r1 b2))]
       [(Atom<? a2 a1)
        (match-define (Node _ l2 r2) b2)
        (Node a2 (-diff b1 l2) (-diff b1 r2))]
       [else
        (match-define (Node _ l1 r1) b1)
        (match-define (Node _ l2 r2) b2)
        (Node a1 (-diff l1 l2) (-diff r1 r2))])]))


(: ->Type (-> TypeSexp BDD))
(define (->Type sexp)
  (match sexp
    ['Univ top]
    ['Empty bot]
    ['Unit (-atom (Tag 0))]
    ['Bool (->Type '(Or T F))]
    ['Str (-atom (Tag 1))]
    ['UnivProd (-atom UnivProd)]
    ['UnivArrow (-atom UnivArrow)]
    ['Int (-atom Int)]
    ['T (-atom (Tag 2))]
    ['F (-atom (Tag 3))]
    ['Nat (-atom Nat)]
    ['PosInt (-atom PosInt)]
    ['NegInt (-atom NegInt)]
    ['UInt8 (-atom UInt8)]
    ['UInt16 (-atom UInt16)]
    ['UInt32 (-atom UInt32)]
    ['Int8 (-atom Int8)]
    ['Int16 (-atom Int16)]
    ['Int32 (-atom Int32)]
    [`(Range ,lower ,upper) (-atom (Range lower upper))]
    [`(Prod ,l ,r) (-atom (Prod (->Type l) (->Type r)))]
    [`(Arrow ,dom ,rng) (-atom (Arrow (->Type dom) (->Type rng)))]
    [`(Or) bot]
    [`(Or ,t . ,ts) (-or (->Type t) (->Type `(Or . ,ts)))]
    [`(And) top]
    [`(And ,t . ,ts) (-and (->Type t) (->Type `(And . ,ts)))]
    [`(Not ,t) (-not (->Type t))]))

