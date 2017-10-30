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



;
;
;
;   ;;;;;;;
;      ;
;      ;
;      ;     ;     ;  ; ;;;      ;;;
;      ;      ;   ;;  ;;   ;    ;   ;
;      ;      ;   ;   ;     ;  ;     ;
;      ;      ;   ;   ;     ;  ;     ;
;      ;       ; ;;   ;     ;  ;;;;;;;
;      ;       ; ;    ;     ;  ;
;      ;        ;;    ;;   ;    ;    ;
;      ;        ;;    ; ;;;      ;;;;
;               ;     ;
;               ;     ;
;             ;;      ;
;



(def-struct Type ([base   : Base]
                  [prods  : (BDD Prod)]
                  [arrows : (BDD Arrow)]))
(: Type<? (-> Type Type Boolean))
(define (Type<? t1 t2)
  (match* (t1 t2)
    [((Type base1 prods1 arrows1)
      (Type base2 prods2 arrows2))
     (cond
       [(Base<? base1 base2) #t]
       [(Base<? base2 base1) #f]
       [(BDD<? prods1 prods2) #t]
       [(BDD<? prods2 prods1) #f]
       [(BDD<? arrows1 arrows2) #t]
       [else #f])]))


(: And (-> Type Type Type))
(define (And t1 t2)
  (match* (t1 t2)
    [((Type base1 prods1 arrows1)
      (Type base2 prods2 arrows2))
     (Type (-base-and base1 base2)
           (-and prods1  prods2)
           (-and arrows1 arrows2))]))

(: And* (-> (Listof Type) Type))
(define (And* ts)
  (foldl And Univ ts))

(: Or (-> Type Type Type))
(define (Or t1 t2)
  (match* (t1 t2)
    [((Type base1 prods1 arrows1)
      (Type base2 prods2 arrows2))
     (Type (-base-or base1 base2)
           (-or prods1  prods2)
           (-or arrows1 arrows2))]))

(: Or* (-> (Listof Type) Type))
(define (Or* ts)
  (foldl Or Empty ts))

(: Diff (-> Type Type Type))
(define (Diff t1 t2)
  (match* (t1 t2)
    [((Type base1 prods1 arrows1)
      (Type base2 prods2 arrows2))
     (Type (-base-diff base1 base2)
           (-diff prods1 prods2)
           (-diff arrows1 arrows2))]))

(: Not (-> Type Type))
(define (Not t)
  (Diff Univ t))




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

(: -base-type (-> Integer Type))
(define (-base-type b)
  (Type (-base-pos b) bot bot))

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
;   ;;;;;;   ;;;;;    ;;;;;
;   ;    ;;  ;   ;;   ;   ;;
;   ;     ;  ;    ;   ;    ;
;   ;     ;  ;     ;  ;     ;
;   ;    ;;  ;     ;  ;     ;
;   ;;;;;    ;     ;  ;     ;
;   ;    ;;  ;     ;  ;     ;
;   ;     ;  ;     ;  ;     ;
;   ;     ;  ;    ;   ;    ;
;   ;    ;;  ;   ;;   ;   ;;
;   ;;;;;;   ;;;;;    ;;;;;
;
;
;
;


(def-struct Prod ([l : Type]
                  [r : Type]))

(def-struct Arrow ([dom : Type]
                   [rng : Type]))

(define-type Atom (U Prod Arrow))

; interp: (Node p l u r) == if p then (l or u) else (r or u)
(def-struct #:∀ (X) Node
  ([a : (∩ X Atom)]
   [l : (BDD X)]
   [u : (BDD X)]
   [r : (BDD X)]))

(define-type (BDD X) (U Top Bot (Node X)))

(define-syntax-rule (with-parameterized-ops X (op ...) . rst)
  (let ([op (inst op X)] ...)
    . rst))

(: Atom<? (-> Atom Atom Boolean))
(define (Atom<? a1 a2)
  (match* (a1 a2)
    [((Prod t1 t2)
      (Prod s1 s2))
     (cond
       [(Type<? t1 s1) #t]
       [(Type<? s1 t1) #f]
       [(Type<? t2 s2) #t]
       [else #f])]
    [((Arrow t1 t2)
      (Arrow s1 s2))
     (cond
       [(Type<? t1 s1) #t]
       [(Type<? s1 t1) #f]
       [(Type<? t2 s2) #t]
       [else #f])]
    [((? Prod?) (? Arrow?)) #t]
    [(_ _) #f]))


(: -node (All (X) (-> (∩ X Atom)
                      (BDD X)
                      (BDD X)
                      (BDD X)
                      (BDD X))))
(define (-node a l u r)
  (cond
    [(Top? u) top]
    [(equal? l r) ((inst -or X) l u)]
    [else ((inst Node X) a l u r)]))


(: -prod-type (-> Type Type Type))
(define (-prod-type l r)
  (Type bot-base (-node (Prod l r) top bot bot) bot))

(: -arrow-type (-> Type Type Type))
(define (-arrow-type l r)
  (Type bot-base bot (-node (Arrow l r) top bot bot)))


(: BDD<? (All (X) (-> (BDD X)
                      (BDD X)
                      Boolean)))
(define (BDD<? b1 b2)
  (match b1
    ;; Top precedes Bot and Node
    [(? Top?) (not (Top? b2))]
    ;; Bot precedes Node
    [(? Bot?) (Node? b2)]
    [(Node p1 _ _ _)
     (match b2
       [(Node p2 _ _ _)
        (cond
          [(Atom<? p1 p2) #t]
          [(Atom<? p2 p1) #f]
          [(BDD<? (Node-l b1)
                  (Node-l b2))
           #t]
          [(BDD<? (Node-l b2)
                  (Node-l b1))
           #f]
          [(BDD<? (Node-u b1)
                  (Node-u b2))
           #t]
          [(BDD<? (Node-u b2)
                  (Node-u b1))
           #f]
          [(BDD<? (Node-r b1)
                  (Node-r b2))
           #t]
          [else #f])]
       [_ #f])]))

(: -or (All (X) (-> (BDD X)
                    (BDD X)
                    (BDD X))))
(define (-or b1 b2)
  (with-parameterized-ops X (-node -or)
    (match* (b1 b2)
      [(b b) b]
      [((? Top?) _) top]
      [(_ (? Top?)) top]
      [((? Bot?) b) b]
      [(b (? Bot?)) b]
      [((Node p1 _ _ _)
        (Node p2 _ _ _))
       (cond
         [(Atom<? p1 p2)
          (match-define (Node _ l1 u1 r1) b1)
          (-node p1 l1 (-or u1 b2) r1)]
         [(Atom<? p2 p1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node p2 l2 (-or b1 u2) r2)]
         [else
          (match-define (Node _ l1 u1 r1) b1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node p1
                 (-or l1 l2)
                 (-or u1 u2)
                 (-or r1 r2))])])))


(: -and (All (X) (-> (BDD X)
                     (BDD X)
                     (BDD X))))
(define (-and b1 b2)
  (with-parameterized-ops X (-node -and -or)
    (match* (b1 b2)
      [(b b) b]
      [((? Top?) b) b]
      [(b (? Top?)) b]
      [((? Bot?) _) bot]
      [(_ (? Bot?)) bot]
      [((Node p1 _ _ _)
        (Node p2 _ _ _))
       (cond
         [(Atom<? p1 p2)
          (match-define (Node _ l1 u1 r1) b1)
          (-node p1
                 (-and l1 b2)
                 (-and u1 b2)
                 (-and r1 b2))]
         [(Atom<? p2 p1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node p2
                 (-and b1 l2)
                 (-and b1 u2)
                 (-and b1 r2))]
         [else
          (match-define (Node _ l1 u1 r1) b1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node p1
                 (-and (-or l1 u1)
                       (-or l2 u2))
                 bot
                 (-and (-or r1 u1)
                       (-or r2 u2)))])])))
(: -neg (All (X) (-> (BDD X) (BDD X))))
(define (-neg b)
  (with-parameterized-ops X (-node -neg -or)
    (match b
      [(? Top?) bot]
      [(? Bot?) top]
      [(Node p l u (? Bot?))
       (-node p
              bot
              (-neg (-or u l))
              (-neg u))]
      [(Node p (? Bot?) u r)
       (-node p
              (-neg u)
              (-neg (-or u r))
              bot)]
      [(Node p l (? Bot?) r)
       (-node p
              (-neg l)
              (-neg (-or l r))
              (-neg l))]
      [(Node p l u r)
       (-node p
              (-neg (-or l u))
              bot
              (-neg (-or r u)))])))

(: -diff (All (X) (-> (BDD X)
                      (BDD X)
                      (BDD X))))
(define (-diff b1 b2)
  (with-parameterized-ops X (-node -or -neg -diff)
    (match* (b1 b2)
      [(b b) bot]
      [(_ (? Top?)) bot]
      [((? Bot?) _) bot]
      [(b (? Bot?)) b]
      [((? Top?) _) (-neg b2)]
      [((Node p1 _ _ _)
        (Node p2 _ _ _))
       (cond
         [(Atom<? p1 p2)
          ;; NOTE: different from paper, consistent w/ CDuce
          (match-define (Node _ l1 u1 r1) b1)
          (-node p1
                 (-diff l1 b2)
                 (-diff u1 b2)
                 (-diff r1 b2))]
         [(Atom<? p2 p1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node p2
                 (-diff b1 (-or l2 u2))
                 bot
                 (-diff b1 (-or r2 u2)))]
         [else
          (match-define (Node _ l1 u1 r1) b1)
          (match-define (Node _ l2 u2 r2) b2)
          (-node p1
                 (-diff l1 l2)
                 (-diff u1 u2)
                 (-diff r1 r2))])])))




;
;
;
;     ;;;;            ;
;   ;;   ;;           ;          ;
;   ;                 ;          ;
;   ;        ;     ;  ; ;;;    ;;;;;;   ;     ;  ; ;;;      ;;;
;   ;;       ;     ;  ;;   ;     ;       ;   ;;  ;;   ;    ;   ;
;     ;;;    ;     ;  ;     ;    ;       ;   ;   ;     ;  ;     ;
;        ;;  ;     ;  ;     ;    ;       ;   ;   ;     ;  ;     ;
;         ;  ;     ;  ;     ;    ;        ; ;;   ;     ;  ;;;;;;;
;   ;     ;  ;     ;  ;     ;    ;        ; ;    ;     ;  ;
;   ;;   ;;  ;;   ;;  ;;   ;     ;         ;;    ;;   ;    ;    ;
;    ;;;;;    ;;;; ;  ; ;;;       ;;;      ;;    ; ;;;      ;;;;
;                                          ;     ;
;                                          ;     ;
;                                        ;;      ;
;



(: subtype? (-> Type Type Boolean))
(define (subtype? t1 t2)
  (empty-Type? (Diff t1 t2)))

(: empty-Type? (-> Type Boolean))
(define (empty-Type? t)
  (match-define (Type base prod arrow) t)
  (and (Bot-base? base)
       (empty-Prod? prod Univ Univ (list))
       (empty-Arrow? arrow Empty (list) (list))))


(: empty-Prod? (-> (BDD Prod) Type Type (Listof Prod)
                   Boolean))
(define (empty-Prod? t s1 s2 N)
  (match t
    [(? Top?) (or (empty-Type? s1)
                  (empty-Type? s2)
                  (Prod-Phi s1 s2 N))]
    [(? Bot?) #t]
    [(Node (and p (Prod t1 t2)) l u r)
     (and (empty-Prod? l (And s1 t1) (And s2 t2) N)
          (empty-Prod? u s1 s2 N)
          (empty-Prod? r s1 s2 (cons p N)))]))

(: Prod-Phi (-> Type Type (Listof Prod) Boolean))
(define (Prod-Phi s1 s2 N)
  (match N
    [(cons (Prod t1 t2) N)
     (and (let ([s1* (Diff s1 t1)])
            (or (empty-Type? s1*)
                (Prod-Phi s1* s2 N)))
          (let ([s2* (Diff s2 t2)])
            (or (empty-Type? s2*)
                (Prod-Phi s1 s2* N))))]
    [_ #f]))


(: empty-Arrow? (-> (BDD Arrow) Type (Listof Arrow) (Listof Arrow)
                    Boolean))
(define (empty-Arrow? t dom P N)
  (match t
    [(? Top?) (ormap (match-lambda
                       [(Arrow t1 t2)
                        (and (subtype? t1 dom)
                             (Arrow-Phi t1 (Not t2) P))])
                     N)]
    [(? Bot?) #t]
    [(Node (and a (Arrow s1 s2)) l u r)
     (and (empty-Arrow? l (Or s1 dom) (cons a P) N)
          (empty-Arrow? u dom P N)
          (empty-Arrow? r dom P (cons a N)))]))


(: Arrow-Phi (-> Type Type (Listof Arrow)
                 Boolean))
(define (Arrow-Phi t1 t2 P)
  (match P
    [(cons (Arrow s1* s2*) P)
     (let ([t1* (Diff t1 s1*)])
       (and (or (empty-Type? t1*)
                (let ([s2 (And* (map Arrow-rng P))])
                  (subtype? s2 (Not t2))))
            (Arrow-Phi t1 (And t2 s2*) P)
            (Arrow-Phi t1* t2 P)))]
    ;; this last clause was just #t from the paper...?
    [_ (or (empty-Type? t1)
           (empty-Type? t2))]))



(define Univ : Type (Type top-base top top))
(define Empty : Type  (Type bot-base bot bot))



(: ->Type (-> TypeSexp Type))
(define (->Type sexp)
  (match sexp
    ['Univ Univ]
    ['Empty Empty]
    ['Unit Unit]
    ['Bool (Or T F)]
    ['Str Str]
    ['UnivProd (-prod-type Univ Univ)]
    ['UnivArrow (-arrow-type Empty Univ)]
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
    [`(Prod ,l ,r) (-prod-type (->Type l) (->Type r))]
    [`(Arrow ,dom ,rng) (-arrow-type (->Type dom) (->Type rng))]
    [`(Or . ,ts) (Or* (map ->Type ts))]
    [`(And . ,ts) (And* (map ->Type ts))]
    [`(Not ,t) (Not (->Type t))]))


(module+ test
  (run-subtype-tests ->Type subtype?)
  )
