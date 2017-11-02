#lang racket/base

;; An implementation of the binary decision diagram (BDD)
;; with lazy unions representation of DNF set-theoretic types
;; from "Covariance and Contravariance: a fresh look at an
;; old issue" (section 4) that computes and caches hash codes
;; ahead of time to reduce the cost of calculating hash
;; codes and equality while subtyping and calculating
;; and/or/diff of types.

(require racket/match
         (only-in racket/unsafe/ops
                  unsafe-fx<
                  unsafe-fxxor
                  unsafe-fx*)
         "subtype-test-suite.rkt")

(provide (all-defined-out))



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

;; Note: Rep is used so all of our internal representations
;; can easily have a 'hash-code' field we can grab,
;; we don't intend to create any 'Rep' directly,
;; just things that inherit from it
(struct Rep (hash-code) #:transparent)

(struct Top Rep () #:transparent)
(define top (Top 15661)) ;; some prime

(struct Bot Rep () #:transparent)
(define bot (Bot 17047)) ;; some prime

(define-syntax hash-xor
  (syntax-rules ()
    [(_ h1 h2) (unsafe-fxxor h1 h2)]
    [(_ h1 h2 . h3) (hash-xor (unsafe-fxxor h1 h2) . h3)]))

(define-syntax-rule (hash<? h1 h2)
  (unsafe-fx< h1 h2))

(define-syntax-rule (hash* h n)
  (unsafe-fx* h n))

; base : Base
; prods : BDD of Prod
; arrows : BDD of Arrow
(struct Type Rep (base prods arrows)
  #:transparent)

; (-> Base (BDD Prod) (BDD Arrow) Type)
(define (-type bs ps as)
  (Type (hash-xor (Rep-hash-code bs)
                  (Rep-hash-code ps)
                  (Rep-hash-code as))
        bs
        ps
        as))

; (-> Type Type Boolean)
(define (Type<? t1 t2)
  (define hc1 (Rep-hash-code t1))
  (define hc2 (Rep-hash-code t2))
  (cond
    [(hash<? hc1 hc2) #t]
    [(hash<? hc2 hc1) #f]
    [else
     (match* (t1 t2)
       [((Type _ base1 prods1 arrows1)
         (Type _ base2 prods2 arrows2))
        (cond
          [(Base<? base1 base2) #t]
          [(Base<? base2 base1) #f]
          [(BDD<? prods1 prods2) #t]
          [(BDD<? prods2 prods1) #f]
          [(BDD<? arrows1 arrows2) #t]
          [else #f])])]))


; (-> Type Type Type)
(define (And t1 t2)
  (match* (t1 t2)
    [((Type _ base1 prods1 arrows1)
      (Type _ base2 prods2 arrows2))
     (-type (-base-and base1 base2)
            (-and prods1  prods2)
            (-and arrows1 arrows2))]))

; (-> (Listof Type) Type)
(define (And* ts)
  (foldl And Univ ts))

; (-> Type Type Type)
(define (Or t1 t2)
  (match* (t1 t2)
    [((Type _ base1 prods1 arrows1)
      (Type _ base2 prods2 arrows2))
     (-type (-base-or base1 base2)
            (-or prods1  prods2)
            (-or arrows1 arrows2))]))

; (-> (Listof Type) Type)
(define (Or* ts)
  (foldl Or Empty ts))

; (-> Type Type Type)
(define (Diff t1 t2)
  (match* (t1 t2)
    [((Type _ base1 prods1 arrows1)
      (Type _ base2 prods2 arrows2))
     (-type (-base-diff base1 base2)
            (-diff prods1 prods2)
            (-diff arrows1 arrows2))]))

; (-> Type Type)
(define (Not t)
  (Diff Univ t))





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

; (-> (Listof Fixnum)
;     (Listof Fixnum)
;     (Listof Fixnum))
(define (list-or xs ys)
  (match* (xs ys)
    [((list) _) ys]
    [(_ (list)) xs]
    [((cons x xs-rst) (cons y ys-rst))
     (cond
       [(unsafe-fx< x y)
        (cons x (list-or xs-rst ys))]
       [(eq? x y)
        (list-or xs-rst ys)]
       [else (cons y (list-or ys-rst xs))])]))

; (-> (Listof Fixnum)
;     (Listof Fixnum)
;     (Listof Fixnum))
(define (list-and xs ys)
  (match* (xs ys)
    [((list) _) '()]
    [(_ (list)) '()]
    [((cons x xs-rst) (cons y ys-rst))
     (cond
       [(unsafe-fx< x y) (list-and xs-rst ys)]
       [(eq? x y) (cons x (list-and xs-rst ys-rst))]
       [else (list-and ys-rst xs)])]))

; (-> (Listof Fixnum)
;     (Listof Fixnum)
;     (Listof Fixnum))
(define (list-diff xs ys)
  (remv* ys xs))


(define (list<? xs ys)
  (match* (xs ys)
    [((cons x xs-rst)
      (cons y ys-rst))
     (cond
       [(unsafe-fx< x y) #t]
       [(eq? x y) (list<? xs-rst ys-rst)]
       [else #f])]
    [(_ (? pair?)) #t]
    [(_ _) #f]))


; interpretation:
; DNF for base types can always be simplified
;; and represented as the following forms
;  (or b₁ b₂ ...) -- i.e. one of
; bits : (Listof Fixnum)
(struct BasePos Rep (bits)
  #:transparent)
; or
; ¬(or b₁ b₂ ...)) -- i.e. none of
; bits : (Listof Fixnum)
(struct BaseNeg Rep (bits)
  #:transparent)

; a Base is (U BasePos BaseNeg)

; (-> (Listof Fixnum) Base)
(define (-base-pos ints)
  (BasePos (foldl unsafe-fxxor 92593 ints) ints))

; (-> (Listof Fixnum) Base)
(define (-base-neg ints)
  (BaseNeg (foldl unsafe-fxxor 94709 ints) ints))

; (-> (Listof Fixnum) Type)
(define (-base-type b)
  (-type (-base-pos b) bot bot))

(define (Base<? b1 b2)
  (define hc1 (Rep-hash-code b1))
  (define hc2 (Rep-hash-code b2))
  (cond
    [(hash<? hc1 hc2) #t]
    [(hash<? hc2 hc1) #f]
    [else
     (match* (b1 b2)
       [((? BasePos?) (? BaseNeg?)) #t]
       [((? BaseNeg?) (? BasePos?)) #f]
       [((BasePos _ bits1)
         (BasePos _ bits2))
        (list<? bits1 bits2)]
       [((BaseNeg _ bits1)
         (BaseNeg _ bits2))
        (list<? bits1 bits2)])]))

(define top-base (-base-neg '()))

(define (Top-base? b)
  (equal? b top-base))


(define bot-base (-base-pos '()))

(define (Bot-base? b)
  (equal? b bot-base))


(define Unit (-base-type (list 31)))
(define Str (-base-type (list 257)))
(define T (-base-type (list 607)))
(define F (-base-type (list 1319)))
(define NegInt<Int32-bits (list 1933))
(define Int32<Int16-bits (list 3343))
(define Int16<Int8-bits (list 4289))
(define Int8<Zero-bits (list 5801))
(define Zero-bits (list 7039))
(define Int8>Zero-bits (list 8293))
(define UInt8>Int8-bits (list 10243))
(define Int16>UInt8-bits (list 11633))
(define UInt16>Int16-bits (list 12281))
(define Int32>UInt16-bits (list 14683))
(define UInt32>Int32-bits (list 16273))
(define PosInt>UInt32-bits (list 17903))

(define UInt8
  (-base-type (sort (append Zero-bits
                            Int8>Zero-bits
                            UInt8>Int8-bits)
                    <)))
(define Int8
  (-base-type (sort (append Int8<Zero-bits
                            Zero-bits
                            Int8>Zero-bits)
                    <)))
(define UInt16
  (-base-type (sort (append Zero-bits
                            Int8>Zero-bits
                            UInt8>Int8-bits
                            Int16>UInt8-bits
                            UInt16>Int16-bits)
                    <)))
(define Int16
  (-base-type (sort (append Int16<Int8-bits
                            Int8<Zero-bits
                            Zero-bits
                            Int8>Zero-bits
                            UInt8>Int8-bits
                            Int16>UInt8-bits)
                    <)))
(define UInt32
  (-base-type (append Zero-bits
                      Int8>Zero-bits
                      UInt8>Int8-bits
                      Int16>UInt8-bits
                      UInt16>Int16-bits
                      Int32>UInt16-bits
                      UInt32>Int32-bits)))
(define Int32
  (-base-type (sort (append Int32<Int16-bits
                            Int16<Int8-bits
                            Int8<Zero-bits
                            Zero-bits
                            Int8>Zero-bits
                            UInt8>Int8-bits
                            Int16>UInt8-bits
                            UInt16>Int16-bits
                            Int32>UInt16-bits
                            UInt32>Int32-bits)
                    <)))

(define PosInt
  (-base-type (sort (append Int8>Zero-bits
                            UInt8>Int8-bits
                            Int16>UInt8-bits
                            UInt16>Int16-bits
                            Int32>UInt16-bits
                            PosInt>UInt32-bits)
                    <)))

(define Nat
  (-base-type (sort (append Zero-bits
                            Int8>Zero-bits
                            UInt8>Int8-bits
                            Int16>UInt8-bits
                            UInt16>Int16-bits
                            Int32>UInt16-bits
                            PosInt>UInt32-bits)
                    <)))

(define NegInt
  (-base-type (sort (append NegInt<Int32-bits
                            Int32<Int16-bits
                            Int16<Int8-bits
                            Int8<Zero-bits)
                    <)))

(define Int
  (-base-type (sort (append NegInt<Int32-bits
                            Int32<Int16-bits
                            Int16<Int8-bits
                            Int8<Zero-bits
                            Zero-bits
                            Int8>Zero-bits
                            UInt8>Int8-bits
                            Int16>UInt8-bits
                            UInt16>Int16-bits
                            Int32>UInt16-bits
                            PosInt>UInt32-bits)
                    <)))


(define (-base-or b1 b2)
  (match* (b1 b2)
    [((BasePos _ pos1) (BasePos _ pos2))
     (-base-pos (list-or pos1 pos2))]
    [((BaseNeg _ neg1) (BaseNeg _ neg2))
     (-base-neg (list-and neg1 neg2))]
    [((BasePos _ pos) (BaseNeg _ neg))
     (-base-neg (list-diff neg pos))]
    [((BaseNeg _ neg) (BasePos _ pos))
     (-base-neg (list-diff neg pos))]))


(define (-base-and t1 t2)
  (match* (t1 t2)
    [((BasePos _ pos1) (BasePos _ pos2))
     (-base-pos (list-and pos1 pos2))]
    [((BaseNeg _ neg1) (BaseNeg _ neg2))
     (-base-neg (list-or neg1 neg2))]
    [((BasePos _ pos) (BaseNeg _ neg))
     (-base-pos (list-diff pos neg))]
    [((BaseNeg _ neg) (BasePos _ pos))
     (-base-pos (list-diff pos neg))]))


(define (-base-diff b1 b2)
  (match* (b1 b2)
    [((BasePos _ pos1) (BasePos _ pos2))
     (-base-pos (list-diff pos1 pos2))]
    [((BaseNeg _ neg1) (BaseNeg _ neg2))
     (-base-pos (list-diff neg2 neg1))]
    [((BasePos _ pos) (BaseNeg _ neg))
     (-base-pos (list-and pos neg))]
    [((BaseNeg _ neg) (BasePos _ pos))
     (-base-neg (list-or pos neg))]))


(define (-base-not b)
  (match b
    [(BasePos _ bits) (-base-neg bits)]
    [(BaseNeg _ bits) (-base-pos bits)]))




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


; l : Type
; r : Type
(struct Prod Rep (l r)
  #:transparent)

; (-> Type Type Prod)
(define (-prod t1 t2)
  (Prod (hash* (hash-xor (Rep-hash-code t1)
                         (Rep-hash-code t2))
               3)
        t1
        t2))

; dom : Type
; rng : Type
(struct Arrow Rep (dom rng)
  #:transparent)

; (-> Type Type Arrow)
(define (-arrow t1 t2)
  (Arrow (hash* (hash-xor (Rep-hash-code t1)
                          (Rep-hash-code t2))
                13)
         t1
         t2))

; interp: (Node p l u r) == if p then (l or u) else (r or u)
; a is a Prod or Arrow,
; l u and r are BDDs
(struct Node Rep (a l u r)
  #:transparent)

; a (BDD X) is a (U Top Bot (Node X))


(define (Atom<? a1 a2)
  (define hc1 (Rep-hash-code a1))
  (define hc2 (Rep-hash-code a2))
  (cond
    [(hash<? hc1 hc2) #t]
    [(hash<? hc2 hc1) #f]
    [else
     (match* (a1 a2)
       [((Prod _ t1 t2)
         (Prod _ s1 s2))
        (cond
          [(Type<? t1 s1) #t]
          [(Type<? s1 t1) #f]
          [(Type<? t2 s2) #t]
          [else #f])]
       [((Arrow _ t1 t2)
         (Arrow _ s1 s2))
        (cond
          [(Type<? t1 s1) #t]
          [(Type<? s1 t1) #f]
          [(Type<? t2 s2) #t]
          [else #f])]
       [((? Prod?) (? Arrow?)) #t]
       [(_ _) #f])]))


(define (-node a l u r)
  (cond
    [(Top? u) top]
    [(equal? l r) (-or l u)]
    [else (Node (hash* (hash-xor (Rep-hash-code a)
                                 (Rep-hash-code l)
                                 (Rep-hash-code u)
                                 (Rep-hash-code r))
                       31)
                a
                l
                u
                r)]))


; (-> Type Type Type)
(define (-prod-type l r)
  (-type bot-base (-node (-prod l r) top bot bot) bot))

; (-> Type Type Type)
(define (-arrow-type l r)
  (-type bot-base bot (-node (-arrow l r) top bot bot)))


(define (BDD<? b1 b2)
  (define hc1 (Rep-hash-code b1))
  (define hc2 (Rep-hash-code b2))
  (cond
    [(hash<? hc1 hc2) #t]
    [(hash<? hc2 hc1) #f]
    [else
     (match b1
       ;; Top precedes Bot and Node
       [(? Top?) (not (Top? b2))]
       ;; Bot precedes Node
       [(? Bot?) (Node? b2)]
       [(Node _ p1 _ _ _)
        (match b2
          [(Node _ p2 _ _ _)
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
          [_ #f])])]))


; (-> BDD BDD BDD)
(define (-or b1 b2)
  (match* (b1 b2)
    [(b b) b]
    [((? Top?) _) top]
    [(_ (? Top?)) top]
    [((? Bot?) b) b]
    [(b (? Bot?)) b]
    [((Node _ p1 _ _ _)
      (Node _ p2 _ _ _))
     (cond
       [(Atom<? p1 p2)
        (match-define (Node _ _ l1 u1 r1) b1)
        (-node p1 l1 (-or u1 b2) r1)]
       [(Atom<? p2 p1)
        (match-define (Node _ _ l2 u2 r2) b2)
        (-node p2 l2 (-or b1 u2) r2)]
       [else
        (match-define (Node _ _ l1 u1 r1) b1)
        (match-define (Node _ _ l2 u2 r2) b2)
        (-node p1
               (-or l1 l2)
               (-or u1 u2)
               (-or r1 r2))])]))

; (-> BDD BDD BDD)
(define (-and b1 b2)
  (match* (b1 b2)
    [(b b) b]
    [((? Top?) b) b]
    [(b (? Top?)) b]
    [((? Bot?) _) bot]
    [(_ (? Bot?)) bot]
    [((Node _ p1 _ _ _)
      (Node _ p2 _ _ _))
     (cond
       [(Atom<? p1 p2)
        (match-define (Node _ _ l1 u1 r1) b1)
        (-node p1
               (-and l1 b2)
               (-and u1 b2)
               (-and r1 b2))]
       [(Atom<? p2 p1)
        (match-define (Node _ _ l2 u2 r2) b2)
        (-node p2
               (-and b1 l2)
               (-and b1 u2)
               (-and b1 r2))]
       [else
        (match-define (Node _ _ l1 u1 r1) b1)
        (match-define (Node _ _ l2 u2 r2) b2)
        (-node p1
               (-and (-or l1 u1)
                     (-or l2 u2))
               bot
               (-and (-or r1 u1)
                     (-or r2 u2)))])]))

; (-> BDD BDD)
(define (-neg b)
  (match b
    [(? Top?) bot]
    [(? Bot?) top]
    [(Node _ p l u (? Bot?))
     (-node p
            bot
            (-neg (-or u l))
            (-neg u))]
    [(Node _ p (? Bot?) u r)
     (-node p
            (-neg u)
            (-neg (-or u r))
            bot)]
    [(Node _ p l (? Bot?) r)
     (-node p
            (-neg l)
            (-neg (-or l r))
            (-neg l))]
    [(Node _ p l u r)
     (-node p
            (-neg (-or l u))
            bot
            (-neg (-or r u)))]))

; (-> BDD BDD BDD)
(define (-diff b1 b2)
  (match* (b1 b2)
    [(b b) bot]
    [(_ (? Top?)) bot]
    [((? Bot?) _) bot]
    [(b (? Bot?)) b]
    [((? Top?) _) (-neg b2)]
    [((Node _ p1 _ _ _)
      (Node _ p2 _ _ _))
     (cond
       [(Atom<? p1 p2)
        ;; NOTE: different from paper, consistent w/ CDuce
        (match-define (Node _ _ l1 u1 r1) b1)
        (-node p1
               (-diff l1 b2)
               (-diff u1 b2)
               (-diff r1 b2))]
       [(Atom<? p2 p1)
        (match-define (Node _ _ l2 u2 r2) b2)
        (-node p2
               (-diff b1 (-or l2 u2))
               bot
               (-diff b1 (-or r2 u2)))]
       [else
        (match-define (Node _ _ l1 u1 r1) b1)
        (match-define (Node _ _ l2 u2 r2) b2)
        (-node p1
               (-diff l1 l2)
               (-diff u1 u2)
               (-diff r1 r2))])]))




(define Univ (-type top-base top top))
(define Empty  (-type bot-base bot bot))


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


