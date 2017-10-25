#lang typed/racket/base

(require racket/match
         (only-in racket/unsafe/ops unsafe-fx<)
         "grammar.rkt"
         "subtype-test-suite.rkt"
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



;
;
;
;   ;;;;;;
;   ;    ;;
;   ;     ;
;   ;     ;    ;;;;    ;;;;;     ;;;
;   ;    ;;   ;    ;  ;     ;   ;   ;
;   ;;;;;          ;  ;        ;     ;
;   ;    ;;   ;;;;;;  ;;;;     ;     ;
;   ;     ;  ;;    ;     ;;;;  ;;;;;;;
;   ;     ;  ;     ;        ;  ;
;   ;    ;;  ;    ;;  ;     ;   ;    ;
;   ;;;;;;    ;;;; ;   ;;;;;     ;;;;
;
;
;
;



; interpretation:
; DNF for base types can always be simplified
;; and represented as the following forms
;  (or b₁ b₂ ...) -- i.e. one of
(def-struct BasePos ([bits : Integer]))
; or
; ¬(or b₁ b₂ ...)) -- i.e. none of
(def-struct BaseNeg ([bits : Integer]))

(define-type Base (U BasePos BaseNeg))

(: -base-pos (-> Integer Base))
(define (-base-pos bits)
  (cond
    [(eqv? bits #b1111111111111111)
     (BaseNeg #b0)]
    [else (BasePos bits)]))

(: -base-neg (-> Integer Base))
(define (-base-neg bits)
  (cond
    [(eqv? bits #b1111111111111111)
     (BasePos #b0)]
    [else (BaseNeg bits)]))

(: Base<? (-> Base Base Boolean))
(define (Base<? b1 b2)
  (match* (b1 b2)
    [((BasePos _) (BaseNeg _)) #t]
    [((BaseNeg _) (BasePos _)) #f]
    [((BasePos bits1)
      (BasePos bits2))
     (< bits1 bits2)]
    [((BaseNeg bits1)
      (BaseNeg bits2))
     (< bits1 bits2)]))

(define top-base (-base-neg #b0))
(: Top-base? (-> Base Boolean))
(define (Top-base? b)
  (equal? b top-base))


(define bot-base (-base-pos #b0))
(: Bot-base? (-> Base Boolean))
(define (Bot-base? b)
  (equal? b bot-base))

(: -base-type (-> Integer Type))
(define (-base-type b)
  (Type (-base-pos b) bot bot))

;; 4 bits for non-numeric base types
(define Unit (-base-type #b1))
(define Str (-base-type #b10))
(define T (-base-type #b100))
(define F (-base-type #b1000))

;; bit 5 and greater for disjoint numeric types
(define NegInt<Int32-bits  #b0000000000010000)
(define Int32<Int16-bits   #b0000000000100000)
(define Int16<Int8-bits    #b0000000001000000)
(define Int8<Zero-bits     #b0000000010000000)
(define Zero-bits          #b0000000100000000)
(define Int8>Zero-bits     #b0000001000000000)
(define UInt8>Int8-bits    #b0000010000000000)
(define Int16>UInt8-bits   #b0000100000000000)
(define UInt16>Int16-bits  #b0001000000000000)
(define Int32>UInt16-bits  #b0010000000000000)
(define UInt32>Int32-bits  #b0100000000000000)
(define PosInt>UInt32-bits #b1000000000000000)
;; now to define the numeric bases
;; that use those bits
(define UInt8
  (-base-type (bitwise-ior Zero-bits
                           Int8>Zero-bits
                           UInt8>Int8-bits)))
(define Int8
  (-base-type (bitwise-ior Int8<Zero-bits
                           Zero-bits
                           Int8>Zero-bits)))
(define UInt16
  (-base-type (bitwise-ior Zero-bits
                           Int8>Zero-bits
                           UInt8>Int8-bits
                           Int16>UInt8-bits
                           UInt16>Int16-bits)))
(define Int16
  (-base-type (bitwise-ior Int16<Int8-bits
                           Int8<Zero-bits
                           Zero-bits
                           Int8>Zero-bits
                           UInt8>Int8-bits
                           Int16>UInt8-bits)))
(define UInt32
  (-base-type (bitwise-ior Zero-bits
                           Int8>Zero-bits
                           UInt8>Int8-bits
                           Int16>UInt8-bits
                           UInt16>Int16-bits
                           Int32>UInt16-bits
                           UInt32>Int32-bits)))
(define Int32
  (-base-type (bitwise-ior Int32<Int16-bits
                           Int16<Int8-bits
                           Int8<Zero-bits
                           Zero-bits
                           Int8>Zero-bits
                           UInt8>Int8-bits
                           Int16>UInt8-bits
                           UInt16>Int16-bits
                           Int32>UInt16-bits
                           UInt32>Int32-bits)))

(define PosInt
  (-base-type (bitwise-ior Int8>Zero-bits
                           UInt8>Int8-bits
                           Int16>UInt8-bits
                           UInt16>Int16-bits
                           Int32>UInt16-bits
                           PosInt>UInt32-bits)))

(define Nat
  (-base-type (bitwise-ior Zero-bits
                           Int8>Zero-bits
                           UInt8>Int8-bits
                           Int16>UInt8-bits
                           UInt16>Int16-bits
                           Int32>UInt16-bits
                           PosInt>UInt32-bits)))

(define NegInt
  (-base-type (bitwise-ior NegInt<Int32-bits
                           Int32<Int16-bits
                           Int16<Int8-bits
                           Int8<Zero-bits)))

(define Int
  (-base-type (bitwise-ior NegInt<Int32-bits
                           Int32<Int16-bits
                           Int16<Int8-bits
                           Int8<Zero-bits
                           Zero-bits
                           Int8>Zero-bits
                           UInt8>Int8-bits
                           Int16>UInt8-bits
                           UInt16>Int16-bits
                           Int32>UInt16-bits
                           PosInt>UInt32-bits)))

                         
(define-syntax-rule (bitwise-subtract b1 b2)
  (bitwise-and b1 (bitwise-not b2)))

(: -base-or (-> Base Base Base))
(define (-base-or b1 b2)
  (match* (b1 b2)
    [((BasePos pos1) (BasePos pos2))
     (-base-pos (bitwise-ior pos1 pos2))]
    [((BaseNeg neg1) (BaseNeg neg2))
     (-base-neg (bitwise-and neg1 neg2))]
    [((BasePos pos) (BaseNeg neg))
     (-base-neg (bitwise-subtract neg pos))]
    [((BaseNeg neg) (BasePos pos))
     (-base-neg (bitwise-subtract neg pos))]))

(: -base-and (-> Base Base Base))
(define (-base-and t1 t2)
  (match* (t1 t2)
    [((BasePos pos1) (BasePos pos2))
     (-base-pos (bitwise-and pos1 pos2))]
    [((BaseNeg neg1) (BaseNeg neg2))
     (-base-neg (bitwise-ior neg1 neg2))]
    [((BasePos pos) (BaseNeg neg))
     (-base-pos (bitwise-subtract pos neg))]
    [((BaseNeg neg) (BasePos pos))
     (-base-pos (bitwise-subtract pos neg))]))


(: -base-diff (-> Base Base Base))
(define (-base-diff b1 b2)
  (match* (b1 b2)
    [((BasePos pos1) (BasePos pos2))
     (-base-pos (bitwise-subtract pos1 pos2))]
    [((BaseNeg neg1) (BaseNeg neg2))
     (-base-pos (bitwise-subtract neg2 neg1))]
    [((BasePos pos) (BaseNeg neg))
     (-base-pos (bitwise-and pos neg))]
    [((BaseNeg neg) (BasePos pos))
     (-base-neg (bitwise-ior pos neg))]))

(: -base-not (-> Base Base))
(define (-base-not b)
  (match b
    [(BasePos bits) (-base-neg bits)]
    [(BaseNeg bits) (-base-pos bits)]))



;
;
;
;   ;;;;;;                           ;
;   ;    ;;                          ;
;   ;     ;                          ;
;   ;     ;    ; ;;;    ;;;      ;;; ;
;   ;     ;    ;;   ;  ;   ;    ;   ;;
;   ;    ;;    ;      ;     ;  ;     ;
;   ;;;;;;     ;      ;     ;  ;     ;
;   ;          ;      ;     ;  ;     ;
;   ;          ;      ;     ;  ;     ;
;   ;          ;       ;   ;    ;   ;;
;   ;          ;        ;;;      ;;; ;
;
;
;
;




(def-struct Prod ([l : Type]
                  [r : Type]))

(define-type ProdBDD (U Top Bot ProdNode))

; interp: (ProdNode p l u r) == if p then (l or u) else (r or u)
(def-struct ProdNode
  ([p : Prod]
   [l : ProdBDD]
   [u  : ProdBDD]
   [r : ProdBDD]))

(: -prod-node (All (X) (-> Prod
                           ProdBDD
                           ProdBDD
                           ProdBDD
                           ProdBDD)))
(define (-prod-node a l u r)
  (cond
    [(Top? u) top]
    [(equal? l r) (-prod-or l u)]
    [else (ProdNode a l u r)]))


(: Prod<? (-> Prod Prod Boolean))
(define (Prod<? p1 p2)
  (match* (p1 p2)
    [((Prod t1 t2)
      (Prod s1 s2))
     (cond
       [(Type<? t1 s1) #t]
       [(Type<? s1 t1) #f]
       [(Type<? t2 s2) #t]
       [else #f])]))

(: ProdBDD<? (-> ProdBDD
                 ProdBDD
                 Boolean))
(define (ProdBDD<? b1 b2)
  (match* (b1 b2)
    [((? Top?) _) (not (Top? b2))]
    [((? Bot?) _) (not (ProdNode? b2))]
    [((ProdNode p1 _ _ _)
      (ProdNode p2 _ _ _))
     (cond
       [(Prod<? p1 p2) #t]
       [(Prod<? p2 p1) #f]
       [(ProdBDD<? (ProdNode-l b1)
                   (ProdNode-l b2))
        #t]
       [(ProdBDD<? (ProdNode-l b2)
                   (ProdNode-l b1))
        #f]
       [(ProdBDD<? (ProdNode-u b1)
                   (ProdNode-u b2))
        #t]
       [(ProdBDD<? (ProdNode-u b2)
                   (ProdNode-u b1))
        #f]
       [(ProdBDD<? (ProdNode-r b1)
                   (ProdNode-r b2))
        #t]
       [else #f])]))

(: -prod-or (-> ProdBDD
                ProdBDD
                ProdBDD))
(define (-prod-or b1 b2)
  (match* (b1 b2)
    [((? Top?) _) top]
    [(_ (? Top?)) top]
    [((? Bot?) b) b]
    [(b (? Bot?)) b]
    [((ProdNode p1 _ _ _)
      (ProdNode p2 _ _ _))
     (cond
       [(Prod<? p1 p2)
        (match-define (ProdNode _ l1 u1 r1) b1)
        (-prod-node p1 l1 (-prod-or u1 b2) r1)]
       [(Prod<? p2 p1)
        (match-define (ProdNode _ l2 u2 r2) b2)
        (-prod-node p2 l2 (-prod-or b1 u2) r2)]
       [else
        (match-define (ProdNode _ l1 u1 r1) b1)
        (match-define (ProdNode _ l2 u2 r2) b2)
        (-prod-node p1
                    (-prod-or l1 l2)
                    (-prod-or u1 u2)
                    (-prod-or r1 r2))])]))


(: -prod-and (-> ProdBDD
                 ProdBDD
                 ProdBDD))
(define (-prod-and b1 b2)
  (match* (b1 b2)
    [((? Top?) b) b]
    [(b (? Top?)) b]
    [((? Bot?) _) bot]
    [(_ (? Bot?)) bot]
    [((ProdNode p1 _ _ _)
      (ProdNode p2 _ _ _))
     (cond
       [(Prod<? p1 p2)
        (match-define (ProdNode _ l1 u1 r1) b1)
        (-prod-node p1
                    (-prod-and l1 b2)
                    (-prod-and u1 b2)
                    (-prod-and r1 b2))]
       [(Prod<? p2 p1)
        (match-define (ProdNode _ l2 u2 r2) b2)
        (-prod-node p2
                    (-prod-and b1 l2)
                    (-prod-and b1 u2)
                    (-prod-and b1 r2))]
       [else
        (match-define (ProdNode _ l1 u1 r1) b1)
        (match-define (ProdNode _ l2 u2 r2) b2)
        (-prod-node p1
                    (-prod-and (-prod-or l1 u1)
                               (-prod-or l2 u2))
                    bot
                    (-prod-and (-prod-or r1 u1)
                               (-prod-or r2 u2)))])]))

(: -prod-diff (-> ProdBDD
                  ProdBDD
                  ProdBDD))
(define (-prod-diff b1 b2)
  (match* (b1 b2)
    [(_ (? Top?)) bot]
    [((? Bot?) _) bot]
    [(b (? Bot?)) b]
    [((? Top?) (ProdNode p l u r))
     ;; this seems right based on non-lazy BDDs
     ;; and it seems to do the right thing...
     (-prod-node p
                 (-prod-diff top (-prod-or l u))
                 bot
                 (-prod-diff top (-prod-or r u)))]
    [((ProdNode p1 _ _ _)
      (ProdNode p2 _ _ _))
     (cond
       [(Prod<? p1 p2)
        ;; the paper says for this case:
        ;; a₁ ? (l₁ ∨ u₁) \ (l₂ ∨ u₂) : ⊥ : (r₁ ∨ u₁) \ (r₂ ∨ u₂)
        ;; but that seems wrong, since it entirely throws away a₂
        ;; this seems like a sensible choice based on the a₂ <  a₁
        ;; case and on what non-lazy BDDs do in this case:
        ;; a₁ ? (l₁ ∨  u₁) \ b₂ : ⊥ : (r₁ ∨  u₁) \ b₂
        (match-define (ProdNode _ l1 u1 r1) b1)
        (-prod-node p1
                    (-prod-diff (-prod-or l1 u1) b2)
                    bot
                    (-prod-diff (-prod-or r1 u1) b2))]
       [(Prod<? p2 p1)
        (match-define (ProdNode _ l2 u2 r2) b2)
        (-prod-node p2
                    (-prod-diff b1 (-prod-or l2 u2))
                    bot
                    (-prod-diff b1 (-prod-or r2 u2)))]
       [else
        (match-define (ProdNode _ l1 u1 r1) b1)
        (match-define (ProdNode _ l2 u2 r2) b2)
        (-prod-node p1
                    (-prod-diff l1 l2)
                    (-prod-diff u1 u2)
                    (-prod-diff r1 r2))])]))





;
;
;
;      ;
;     ; ;
;     ; ;
;     ; ;      ; ;;;    ; ;;;    ;;;   ;       ;
;     ; ;      ;;   ;   ;;   ;  ;   ;  ;       ;
;    ;   ;     ;        ;      ;     ;  ;  ;  ;
;    ;   ;     ;        ;      ;     ;  ;  ;  ;
;    ;;;;;     ;        ;      ;     ;  ; ; ; ;
;    ;   ;     ;        ;      ;     ;  ; ; ; ;
;   ;     ;    ;        ;       ;   ;    ;   ;
;   ;     ;    ;        ;        ;;;     ;   ;
;
;
;
;




(def-struct Arrow ([dom : Type]
                   [rng : Type]))

(define-type ArrowBDD (U Top Bot ArrowNode))

; interp: (ProdNode p l u r) == if p then (l or u) else (r or u)
(def-struct ArrowNode
  ([a : Arrow]
   [l : ArrowBDD]
   [u  : ArrowBDD]
   [r : ArrowBDD]))

(: -arrow-node (All (X) (-> Arrow
                            ArrowBDD
                            ArrowBDD
                            ArrowBDD
                            ArrowBDD)))
(define (-arrow-node a l u r)
  (cond
    [(Top? u) top]
    [(equal? l r) (-arrow-or l u)]
    [else (ArrowNode a l u r)]))


(: ArrowBDD<? (-> ArrowBDD
                  ArrowBDD
                  Boolean))
(define (ArrowBDD<? b1 b2)
  (match* (b1 b2)
    [((? Top?) _) (not (Top? b2))]
    [((? Bot?) _) (not (ProdNode? b2))]
    [((ArrowNode (Arrow t1 t2) _ _ _)
      (ArrowNode (Arrow s1 s2) _ _ _))
     (cond
       [(Type<? t1 s1) #t]
       [(Type<? s1 t1) #f]
       [(Type<? t2 s2) #t]
       [(Type<? s2 t2) #f]
       [(ArrowBDD<? (ArrowNode-l b1)
                    (ArrowNode-l b2))
        #t]
       [(ArrowBDD<? (ArrowNode-l b2)
                    (ArrowNode-l b1))
        #f]
       [(ArrowBDD<? (ArrowNode-u b1)
                    (ArrowNode-u b2))
        #t]
       [(ArrowBDD<? (ArrowNode-u b2)
                    (ArrowNode-u b1))
        #f]
       [(ArrowBDD<? (ArrowNode-r b1)
                    (ArrowNode-r b2))
        #t]
       [else #f])]))

(: -arrow-or (-> ArrowBDD
                 ArrowBDD
                 ArrowBDD))
(define (-arrow-or b1 b2)
  (error 'todo))


(: -arrow-and (-> ArrowBDD
                  ArrowBDD
                  ArrowBDD))
(define (-arrow-and b1 b2)
  (error 'todo))

(: -arrow-diff (-> ArrowBDD
                   ArrowBDD
                   ArrowBDD))
(define (-arrow-diff b1 b2)
  (error 'todo))




(def-struct Type ([base   : Base]
                  [prods  : ProdBDD]
                  [arrows : ArrowBDD]))
(: Type<? (-> Type Type Boolean))
(define (Type<? t1 t2)
  (match* (t1 t2)
    [((Type base1 prods1 arrows1)
      (Type base2 prods2 arrows2))
     (cond
       [(Base<? base1 base2) #t]
       [(Base<? base2 base1) #f]
       [(ProdBDD<? prods1 prods2) #t]
       [(ProdBDD<? prods2 prods1) #f]
       [(ArrowBDD<? arrows1 arrows2) #t]
       [else #f])]))

;;(struct Var ())
;;(struct Rec ([x : Var] [t : Atom]) #:transparent)
;
;
;(define Univ : Type (Type top-base top top))
;(define Empty : Type  (Type bot-base bot bot))
;
;
;
;(: -prod (-> Type Type Type))
;(define (-prod fst snd)
;  (Type bot-base (Node (Prod fst snd) top bot bot) bot))
;
;(: -arrow (-> Type Type Type))
;(define (-arrow dom rng)
;  (Type bot-base bot (Node (Arrow dom rng) top bot bot)))
;
;
;(define-type (BDD X) (U Top Bot (Node X)))
;

;
;(: -and (All (X) (-> (BDD X) (BDD X) (BDD X))))
;(define (-and b1 b2)
;  (with-parameterized-ops X (-node -and -or)
;    (match* (b1 b2)
;      [((? Top?) b) b]
;      [(b (? Top?)) b]
;      [((? Bot?) _) bot]
;      [(_ (? Bot?)) bot]
;      [((Node a1 _ _ _) (Node a2 _ _ _))
;       (cond
;         [(Atom<? a1 a2)
;          (match-define (Node _ l1 u1 r1) b1)
;          (-node a1
;                 (-and l1 b2)
;                 (-and u1 b2)
;                 (-and r1 b2))]
;         [(Atom<? a2 a1)
;          (match-define (Node _ l2 u2 r2) b2)
;          (-node a2
;                 (-and b1 l2)
;                 (-and b1 u2)
;                 (-and b1 r2))]
;         [else
;          (match-define (Node _ l1 u1 r1) b1)
;          (match-define (Node _ l2 u2 r2) b2)
;          (-node a1
;                 (-and (-or l1 u1)
;                       (-or l2 u2))
;                 bot
;                 (-and (-or r1 u1)
;                       (-or r2 u2)))])])))
;
;(: -or (All (X) (-> (BDD X) (BDD X) (BDD X))))
;(define (-or b1 b2)
;  (with-parameterized-ops X (-node -or)
;    (match* (b1 b2)
;      [((? Top?) _) top]
;      [(_ (? Top?)) top]
;      [((? Bot?) b) b]
;      [(b (? Bot?)) b]
;      [((Node a1 _ _ _) (Node a2 _ _ _))
;       (cond
;         [(Atom<? a1 a2)
;          (match-define (Node _ l1 u1 r1) b1)
;          (-node a1 l1 (-or u1 b2) r1)]
;         [(Atom<? a2 a1)
;          (match-define (Node _ l2 u2 r2) b2)
;          (-node a2 l2 (-or b1 u2) r2)]
;         [else
;          (match-define (Node _ l1 u1 r1) b1)
;          (match-define (Node _ l2 u2 r2) b2)
;          (-node a1
;                 (-or l1 l2)
;                 (-or u1 u2)
;                 (-or r1 r2))])])))
;
;(: -not (All (X) (-> (BDD X) (BDD X))))
;(define (-not b) ((inst -diff X) top b))
;
;(: -diff (All (X) (-> (BDD X) (BDD X) (BDD X))))
;(define (-diff b1 b2)
;  (with-parameterized-ops X (-node -diff -or -and)
;    (match* (b1 b2)
;      [(_ (? Top?)) bot]
;      [((? Bot?) _) bot]
;      [(b (? Bot?)) b]
;      [((? Top?) (Node a l u r))
;       ;; this seems right based on non-lazy BDDs
;       ;; and it seems to do the right thing...
;       (-node a
;              (-diff top (-or l u))
;              bot
;              (-diff top (-or r u)))]
;      [((Node a1 _ _ _) (Node a2 _ _ _))
;       (cond
;         [(Atom<? a1 a2)
;          ;; the paper says for this case:
;          ;; a₁ ? (l₁ ∨ u₁) \ (l₂ ∨ u₂) : ⊥ : (r₁ ∨ u₁) \ (r₂ ∨ u₂)
;          ;; but that seems wrong, since it entirely throws away a₂
;          ;; this seems like a sensible choice based on the a₂ <  a₁
;          ;; case and on what non-lazy BDDs do in this case:
;          ;; a₁ ? (l₁ ∨  u₁) \ b₂ : ⊥ : (r₁ ∨  u₁) \ b₂
;          (match-define (Node _ l1 u1 r1) b1)
;          (-node a1
;                 (-diff (-or l1 u1) b2)
;                 bot
;                 (-diff (-or r1 u1) b2))]
;         [(Atom<? a2 a1)
;          (match-define (Node _ l2 u2 r2) b2)
;          (-node a2
;                 (-diff b1 (-or l2 u2))
;                 bot
;                 (-diff b1 (-or r2 u2)))]
;         [else
;          (match-define (Node _ l1 u1 r1) b1)
;          (match-define (Node _ l2 u2 r2) b2)
;          (-node a1
;                 (-diff l1 l2)
;                 (-diff u1 u2)
;                 (-diff r1 r2))])])))
;
;(: And (-> Type Type Type))
;(define (And t1 t2)
;  (match* (t1 t2)
;    [((Type base1 prods1 arrows1)
;      (Type base2 prods2 arrows2))
;     (Type (-base-and base1 base2)
;           (-and prods1  prods2)
;           (-and arrows1 arrows2))]))
;
;(: Or (-> Type Type Type))
;(define (Or t1 t2)
;  (match* (t1 t2)
;    [((Type base1 prods1 arrows1)
;      (Type base2 prods2 arrows2))
;     (Type (-base-or base1 base2)
;           (-or prods1  prods2)
;           (-or arrows1 arrows2))]))
;
;(: Diff (-> Type Type Type))
;(define (Diff t1 t2)
;  (match* (t1 t2)
;    [((Type base1 prods1 arrows1)
;      (Type base2 prods2 arrows2))
;     (Type (-base-diff base1 base2)
;           (-diff prods1 prods2)
;           (-diff arrows1 arrows2))]))
;
;(: Not (-> Type Type))
;(define (Not t)
;  (Diff Univ t))
;
;
;
;
;
;
;
;(: subtype? (-> Type Type Boolean))
;(define (subtype? t1 t2)
;  (uninhabited-Type? (Diff t1 t2)))
;
;(: uninhabited-Type? (-> Type Boolean))
;(define (uninhabited-Type? t)
;  (match-define (Type base prods arrows) t)
;  (and (Bot-base? base)
;       #;#;(empty-Prod-BDD? prods)
;       (empty-Arrow-BDD? arrows)))
;
;
;(: empty-Prod-BDD?
;   (-> (BDD Prod) Boolean))
;(define (empty-Prod-BDD? t)
;  (error 'todo)
;  #;(let ([s1 (And (map Prod-l P))]
;          [s2 (And (map Prod-r P))])
;      (or (subtype? s1 Empty)
;          (subtype? s2 Empty)
;          (Prod-Phi s1 s2 N))))
;
;#;#;
;(: Prod-Phi (-> Type Type (Setof (Not Prod)) Boolean))
;(define (Prod-Phi s1 s2 N)
;  (error 'todo)
;  #;(match N
;      [(cons (Not (Prod t1 t2)) N)
;       (and (or (subtype? s1 t1)
;                (Prod-Phi (Diff s1 t1) s2 N))
;            (or (subtype? s2 t2)
;                (Prod-Phi s1 (Diff s2 t2) N)))]
;      [_ #f]))
;
;#;#;
;(: empty-Arrow-BDD?
;   (-> (BDD Arrow) Boolean))
;(define (empty-Arrow-BDD? P N)
;  (error 'todo)
;  #;(let ([dom (Or (map Arrow-dom P))])
;      (exists (λ ([na : (Not Arrow)])
;                (let ([t1 (Arrow-dom (Not-t na))]
;                      [t2 (Arrow-rng (Not-t na))])
;                  (and (subtype? t1 dom)
;                       (Arrow-Phi t1 (Not t2) P))))
;              N)))
;
;#;#;
;(: Arrow-Phi (-> Type Type (Setof Arrow)
;                 Boolean))
;(define (Arrow-Phi t1 t2 P)
;  (error 'todo)
;  #;(match P
;      [(cons (Arrow s1* s2*) P)
;       (and (or (subtype? t1 s1*)
;                (let ([s2 (And (map Arrow-rng P))])
;                  (subtype? s2 (Not t2))))
;            (Arrow-Phi t1 (And (set t2 s2*)) P)
;            (Arrow-Phi (Diff t1 s1*) t2 P))]
;      [_ #t]))
;
;
;
;(: ->Type (-> TypeSexp Type))
;(define (->Type sexp)
;  (match sexp
;    ['Univ Univ]
;    ['Empty Empty]
;    ['Unit Unit]
;    ['Bool (Or T F)]
;    ['Str Str]
;    ['UnivProd (-prod Univ Univ)]
;    ['UnivArrow (-arrow Empty Univ)]
;    ['Int Int]
;    ['T T]
;    ['F F]
;    ['Nat Nat]
;    ['PosInt PosInt]
;    ['NegInt NegInt]
;    ['UInt8 UInt8]
;    ['UInt16 UInt16]
;    ['UInt32 UInt32]
;    ['Int8 Int8]
;    ['Int16 Int16]
;    ['Int32 Int32]
;    [`(Prod ,l ,r) (-prod (->Type l) (->Type r))]
;    [`(Arrow ,dom ,rng) (-arrow (->Type dom) (->Type rng))]
;    [`(Or . ,ts) (foldl (λ ([sexp : TypeSexp] [t : Type])
;                          (Or (->Type sexp) t))
;                        Empty
;                        ts)]
;    [`(And . ,ts) (foldl (λ ([sexp : TypeSexp] [t : Type])
;                          (And (->Type sexp) t))
;                        Univ
;                        ts)]
;    [`(Not ,t) (Not (->Type t))]))
;
;
;(module+ test
;  ;(check-false (subtype? (Arrow Int Univ) (Arrow Int Int)))
;  (run-subtype-tests ->Type subtype?)
;  )
