#lang typed/racket/base

(require racket/match
         (only-in racket/unsafe/ops unsafe-fx<)
         "grammar.rkt"
         "tunit.rkt")

(provide (all-defined-out))

(define-syntax def-struct
  (syntax-rules ()
    [(_ name (fld ...))
     (struct name (fld ...) #:transparent)]
    [(_ #:∀ (poly-ids ...) name (fld ...))
     (struct (poly-ids ...) name (fld ...) #:transparent)]))

(define top 'Top)
(define bot 'Bot)
(define-type Top 'Top)
(define-predicate Top? Top)
(define-type Bot 'Bot)
(define-predicate Bot? Bot)

(def-struct Tag ([id : Fixnum]))
(def-struct Range ([lower : Real]
                   [upper : Real]))
(def-struct Prod ([l : Type]
                  [r : Type]))
(def-struct Arrow ([dom : Type]
                   [rng : Type]))

(define-type Atom (U Tag Range Prod Arrow))

(: -atom (All (X) (-> (∩ X Atom) (BDD X))))
(define (-atom t) ((inst Node X) t top bot bot))

; interp: (Node a l u r) == if a then (l or u) else (r or u)
(def-struct #:∀ (X) Node
  ([atom   : (∩ X Atom)]
   [lchild : (BDD (∩ X Atom))]
   [union  : (BDD (∩ X Atom))]
   [rchild : (BDD (∩ X Atom))]))

(: -node (All (X) (-> (∩ X Atom)
                      (BDD (∩ X Atom))
                      (BDD (∩ X Atom))
                      (BDD (∩ X Atom))
                      (BDD (∩ X Atom)))))
(define (-node a l u r)
  (cond
    [(Top? u) top]
    [(equal? l r) ((inst -or X) l u)]
    [else ((inst Node X) a l u r)]))

(define-type (BDD X) (U Top Bot (Node X)))

(def-struct Type ([tags : (BDD Tag)]
                  [ranges : (BDD Range)]
                  [prods : (BDD Prod)]
                  [arrows : (BDD Arrow)]))

(define-syntax-rule (with-parameterized-ops X (op ...) . rst)
  (let ([op (inst op X)] ...)
    . rst))

;(struct Var ())
;(struct Rec ([x : Var] [t : Atom]) #:transparent)


(define Univ : Type (Type top top top top))
(define Empty : Type  (Type bot bot bot bot))

(: -tag (-> Fixnum Type))
(define (-tag n)
  (Type (-atom (Tag n)) bot bot bot))

(: -range (-> Real Real Type))
(define (-range l u)
  (Type bot (-atom (Range l u)) bot bot))

(: -prod (-> Type Type Type))
(define (-prod fst snd)
  (Type bot bot (-atom (Prod fst snd)) bot))

(: -arrow (-> Type Type Type))
(define (-arrow dom rng)
  (Type bot bot bot (-atom (Arrow dom rng))))


(: Atom<? (-> Atom Atom Boolean))
(define (Atom<? a1 a2)
  (match a1
    [(Tag n1)
     (match a2
       [(Tag n2) (unsafe-fx< n1 n2)]
       [_ #t])]
    [(Range l1 u1)
     (match a2
       [(? Tag?) #f]
       [(Range l2 u2)
        (cond
          [(< l1 l2) #t]
          [(> l1 l2) #f]
          [(< u1 u2) #t]
          [else #f])]
       [_ #t])]
    [(Prod l1 r1)
     (match a2
       [(? Tag?) #f]
       [(? Range?) #f]
       [(Prod l2 r2)
        (cond
          [(Type<? l1 l2) #t]
          [(Type<? l2 l1) #f]
          [(Type<? r1 r2) #t]
          [else #f])]
       [_ #t])]
    [(Arrow d1 r1)
     (match a2
       [(Arrow d2 r2)
        (cond
          [(Type<? d1 d2) #t]
          [(Type<? d2 d1) #f]
          [(Type<? r1 r2) #t]
          [else #f])]
       [_ #f])]))

(: BDD<? (All (X) (-> (BDD X) (BDD X) Boolean)))
(define (BDD<? b1 b2)
  (match b1
    [(? Top?) (not (Top? b2))]
    [(? Bot?) (Node? b2)]
    [(Node a1 l1 u1 r1)
     (match b2
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


(: Type<? (-> Type Type Boolean))
(define (Type<? t1 t2)
  (match* (t1 t2)
    [((Type tags1 ranges1 prods1 arrows1)
      (Type tags2 ranges2 prods2 arrows2))
     (cond
       [(BDD<? tags1 tags2) #t]
       [(BDD<? tags2 tags1) #f]
       [(BDD<? ranges1 ranges2) #t]
       [(BDD<? ranges2 ranges1) #f]
       [(BDD<? prods1 prods2) #t]
       [(BDD<? prods2 prods1) #f]
       [(BDD<? arrows1 arrows2) #t]
       [else #f])]))

(: -and (All (X) (-> (BDD X) (BDD X) (BDD X))))
(define (-and b1 b2)
  (with-parameterized-ops X (-node -and -or)
    (match* (b1 b2)
      [((? Top?) b) b]
      [(b (? Top?)) b]
      [((? Bot?) _) bot]
      [(_ (? Bot?)) bot]
      [((Node a1 _ _ _) (Node a2 _ _ _))
       (cond
         [(Atom<? a1 a2)
          (match-define (Node _ l1 u1 r1) b1)
          (-node a1
                 (-and l1 b2)
                 (-and u1 b2)
                 (-and r1 b2))]
         [(Atom<? a2 a1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node a2
                 (-and b1 l2)
                 (-and b1 u2)
                 (-and b1 r2))]
         [else
          (match-define (Node _ l1 u1 r1) b1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node a1
                 (-and (-or l1 u1)
                       (-or l2 u2))
                 bot
                 (-and (-or r1 u1)
                       (-or r2 u2)))])])))

(: -or (All (X) (-> (BDD X) (BDD X) (BDD X))))
(define (-or b1 b2)
  (with-parameterized-ops X (-node -or)
    (match* (b1 b2)
      [((? Top?) _) top]
      [(_ (? Top?)) top]
      [((? Bot?) b) b]
      [(b (? Bot?)) b]
      [((Node a1 _ _ _) (Node a2 _ _ _))
       (cond
         [(Atom<? a1 a2)
          (match-define (Node _ l1 u1 r1) b1)
          (-node a1 l1 (-or u1 b2) r1)]
         [(Atom<? a2 a1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node a2 l2 (-or b1 u2) r2)]
         [else
          (match-define (Node _ l1 u1 r1) b1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node a1
                 (-or l1 l2)
                 (-or u1 u2)
                 (-or r1 r2))])])))

(: -not (All (X) (-> (BDD X) (BDD X))))
(define (-not b) ((inst -diff X) top b))

(: -diff (All (X) (-> (BDD X) (BDD X) (BDD X))))
(define (-diff b1 b2)
  (with-parameterized-ops X (-node -diff -or -and)
    (match* (b1 b2)
      [(_ (? Top?)) bot]
      [((? Bot?) _) bot]
      [(b (? Bot?)) b]
      [((? Top?) (Node a l u r))
       ;; this seems right based on non-lazy BDDs
       ;; and it seems to do the right thing...
       (-node a
              (-diff top (-or l u))
              bot
              (-diff top (-or r u)))]
      [((Node a1 _ _ _) (Node a2 _ _ _))
       (cond
         [(Atom<? a1 a2)
          ;; the paper says for this case:
          ;; a₁ ? (l₁ ∨ u₁) \ (l₂ ∨ u₂) : ⊥ : (r₁ ∨ u₁) \ (r₂ ∨ u₂)
          ;; but that seems wrong, since it entirely throws away a₂
          ;; this seems like a sensible choice based on the a₂ <  a₁
          ;; case and on what non-lazy BDDs do in this case:
          ;; a₁ ? (l₁ ∨  u₁) \ b₂ : ⊥ : (r₁ ∨  u₁) \ b₂
          (match-define (Node _ l1 u1 r1) b1)
          (-node a1
                 (-diff (-or l1 u1) b2)
                 bot
                 (-diff (-or r1 u1) b2))]
         [(Atom<? a2 a1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node a2
                 (-diff b1 (-or l2 u2))
                 bot
                 (-diff b1 (-or r2 u2)))]
         [else
          (match-define (Node _ l1 u1 r1) b1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node a1
                 (-diff l1 l2)
                 (-diff u1 u2)
                 (-diff r1 r2))])])))

(: And (-> Type Type Type))
(define (And t1 t2)
  (match* (t1 t2)
    [((Type tags1 ranges1 prods1 arrows1)
      (Type tags2 ranges2 prods2 arrows2))
     (Type (-and tags1   tags2)
           (-and ranges1 ranges2)
           (-and prods1  prods2)
           (-and arrows1 arrows2))]))

(: Or (-> Type Type Type))
(define (Or t1 t2)
  (match* (t1 t2)
    [((Type tags1 ranges1 prods1 arrows1)
      (Type tags2 ranges2 prods2 arrows2))
     (Type (-or tags1   tags2)
           (-or ranges1 ranges2)
           (-or prods1  prods2)
           (-or arrows1 arrows2))]))

(: Diff (-> Type Type Type))
(define (Diff t1 t2)
  (match* (t1 t2)
    [((Type tags1 ranges1 prods1 arrows1)
      (Type tags2 ranges2 prods2 arrows2))
     (Type (-diff tags1   tags2)
           (-diff ranges1 ranges2)
           (-diff prods1  prods2)
           (-diff arrows1 arrows2))]))

(: Not (-> Type Type))
(define (Not t)
  (Diff Univ t))


(define UnivProd (-prod Univ Univ))
(define UnivArrow (-arrow Empty Univ))
(define Int (-range -inf.0 +inf.0))
(define Nat (-range 0 +inf.0))
(define PosInt (-range 1 +inf.0))
(define NegInt (-range -inf.0 -1))
(define UInt8 (-range 0 255))
(define UInt16 (-range 0 65535))
(define UInt32 (-range 0 4294967295))
(define Int8 (-range -128 127))
(define Int16 (-range -32768 32767))
(define Int32 (-range -2147483648 2147483647))
(define Unit (-tag 0))
(define Str (-tag 1))
(define T (-tag 2))
(define F (-tag 3))
(define Bool (Or T F))


(: ->Type (-> TypeSexp Type))
(define (->Type sexp)
  (match sexp
    ['Univ Univ]
    ['Empty Empty]
    ['Unit Unit]
    ['Bool (->Type '(Or T F))]
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
    [`(Range ,lower ,upper) (-range lower upper)]
    [`(Prod ,l ,r) (-prod (->Type l) (->Type r))]
    [`(Arrow ,dom ,rng) (-arrow (->Type dom) (->Type rng))]
    [`(Or) Empty]
    [`(Or ,t . ,ts) (Or (->Type t) (->Type `(Or . ,ts)))]
    [`(And) Univ]
    [`(And ,t . ,ts) (And (->Type t) (->Type `(And . ,ts)))]
    [`(Not ,t) (Not (->Type t))]))

(: subtype? (-> Type Type Type))
(define (subtype? t1 t2)
  (Diff t1 t2))


;; These all seem to have reasonable results now:
;; (Diff T T) ==>
;;    (Type bot bot bot bot)
;; (Diff F T) ==>
;;   (Type (Node T) bot bot (Node T top bot bot))
;; (Not Bool) ==>
;;   (Type (Node T bot bot (Node F bot bot top)) top top top))