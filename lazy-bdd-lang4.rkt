#lang typed/racket/base

(require racket/match
         (only-in racket/unsafe/ops
                  unsafe-fx<
                  unsafe-fxxor
                  unsafe-fx*)
         "grammar.rkt"
         "subtype-test-suite.rkt"
         "tunit.rkt")

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
(struct Rep ([hash-code : Fixnum]) #:transparent)

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

(struct Type Rep ([base   : Base]
                  [prods  : (BDD Prod)]
                  [arrows : (BDD Arrow)])
  #:transparent)

(: -type (-> Base (BDD Prod) (BDD Arrow) Type))
(define (-type bs ps as)
  (Type (hash-xor (Rep-hash-code bs)
                  (Rep-hash-code ps)
                  (Rep-hash-code as))
        bs
        ps
        as))

(: Type<? (-> Type Type Boolean))
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


(: And (-> Type Type Type))
(define (And t1 t2)
  (match* (t1 t2)
    [((Type _ base1 prods1 arrows1)
      (Type _ base2 prods2 arrows2))
     (-type (-base-and base1 base2)
            (-and prods1  prods2)
            (-and arrows1 arrows2))]))

(: And* (-> (Listof Type) Type))
(define (And* ts)
  (foldl And Univ ts))

(: Or (-> Type Type Type))
(define (Or t1 t2)
  (match* (t1 t2)
    [((Type _ base1 prods1 arrows1)
      (Type _ base2 prods2 arrows2))
     (-type (-base-or base1 base2)
            (-or prods1  prods2)
            (-or arrows1 arrows2))]))

(: Or* (-> (Listof Type) Type))
(define (Or* ts)
  (foldl Or Empty ts))

(: Diff (-> Type Type Type))
(define (Diff t1 t2)
  (match* (t1 t2)
    [((Type _ base1 prods1 arrows1)
      (Type _ base2 prods2 arrows2))
     (-type (-base-diff base1 base2)
            (-diff prods1 prods2)
            (-diff arrows1 arrows2))]))

(: Not (-> Type Type))
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

(: list-or (-> (Listof Fixnum)
               (Listof Fixnum)
               (Listof Fixnum)))
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

(: list-and (-> (Listof Fixnum)
                (Listof Fixnum)
                (Listof Fixnum)))
(define (list-and xs ys)
  (match* (xs ys)
    [((list) _) '()]
    [(_ (list)) '()]
    [((cons x xs-rst) (cons y ys-rst))
     (cond
       [(unsafe-fx< x y) (list-and xs-rst ys)]
       [(eq? x y) (cons x (list-and xs-rst ys-rst))]
       [else (list-and ys-rst xs)])]))

(: list-diff (-> (Listof Fixnum)
                 (Listof Fixnum)
                 (Listof Fixnum)))
(define (list-diff xs ys)
  (remv* ys xs))

(: list<? (-> (Listof Fixnum)
              (Listof Fixnum)
              Boolean))
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
(struct BasePos Rep ([bits : (Listof Fixnum)])
  #:transparent)
; or
; ¬(or b₁ b₂ ...)) -- i.e. none of
(struct BaseNeg Rep ([bits : (Listof Fixnum)])
  #:transparent)

(define-type Base (U BasePos BaseNeg))

(: -base-pos (-> (Listof Fixnum) Base))
(define (-base-pos ints)
  (BasePos (foldl unsafe-fxxor 92593 ints) ints))

(: -base-neg (-> (Listof Fixnum) Base))
(define (-base-neg ints)
  (BaseNeg (foldl unsafe-fxxor 94709 ints) ints))

(: -base-type (-> (Listof Fixnum) Type))
(define (-base-type b)
  (-type (-base-pos b) bot bot))

(: Base<? (-> Base Base Boolean))
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
(: Top-base? (-> Base Boolean))
(define (Top-base? b)
  (equal? b top-base))


(define bot-base (-base-pos '()))
(: Bot-base? (-> Base Boolean))
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


(: -base-or (-> Base Base Base))
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

(: -base-and (-> Base Base Base))
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


(: -base-diff (-> Base Base Base))
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

(: -base-not (-> Base Base))
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


(struct Prod Rep ([l : Type]
                  [r : Type])
  #:transparent)

(: -prod (-> Type Type Prod))
(define (-prod t1 t2)
  (Prod (hash* (hash-xor (Rep-hash-code t1)
                         (Rep-hash-code t2))
               3)
        t1
        t2))

(struct Arrow Rep ([dom : Type]
                   [rng : Type])
  #:transparent)

(: -arrow (-> Type Type Arrow))
(define (-arrow t1 t2)
  (Arrow (hash* (hash-xor (Rep-hash-code t1)
                          (Rep-hash-code t2))
                13)
         t1
         t2))

(define-type Atom (U Prod Arrow))

; interp: (Node p l u r) == if p then (l or u) else (r or u)
(struct (X) Node Rep
  ([a : (∩ X Atom)]
   [l : (BDD X)]
   [u : (BDD X)]
   [r : (BDD X)])
  #:transparent)

(define-type (BDD X) (U Top Bot (Node X)))

(define-syntax-rule (with-parameterized-ops X (op ...) . rst)
  (let ([op (inst op X)] ...)
    . rst))

(: Atom<? (-> Atom Atom Boolean))
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


(: -node (All (X) (-> (∩ X Atom)
                      (BDD X)
                      (BDD X)
                      (BDD X)
                      (BDD X))))
(define (-node a l u r)
  (cond
    [(Top? u) top]
    [(equal? l r) ((inst -or X) l u)]
    [else ((inst Node X) (hash* (hash-xor (Rep-hash-code a)
                                          (Rep-hash-code l)
                                          (Rep-hash-code u)
                                          (Rep-hash-code r))
                                31)
                         a
                         l
                         u
                         r)]))


(: -prod-type (-> Type Type Type))
(define (-prod-type l r)
  (-type bot-base (-node (-prod l r) top bot bot) bot))

(: -arrow-type (-> Type Type Type))
(define (-arrow-type l r)
  (-type bot-base bot (-node (-arrow l r) top bot bot)))


(: BDD<? (All (X) (-> (BDD X)
                      (BDD X)
                      Boolean)))
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
                       (-or r2 u2)))])])))

(: -neg (All (X) (-> (BDD X) (BDD X))))
(define (-neg b)
  (with-parameterized-ops X (-node -neg -or)
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

(define empty-type-cache
  : (Mutable-HashTable Fixnum (Listof (Pairof Type Boolean)))
  (make-hasheq))

(: empty-Type? (-> Type Boolean))
(define (empty-Type? t)
  (define hc (Rep-hash-code t))
  (define bucket (hash-ref empty-type-cache hc #f))
  (cond
    [(and bucket (assoc t bucket)) => cdr]
    [else
     (match-define (Type _ base prod arrow) t)
     (define res
       (and (Bot-base? base)
            (empty-Prod? prod Univ Univ (list))
            (empty-Arrow? arrow Empty (list) (list))))
     (hash-set! empty-type-cache
                hc
                (if bucket
                    (cons (cons t res) bucket)
                    (list (cons t res))))
     res]))


(: empty-Prod? (-> (BDD Prod) Type Type (Listof Prod)
                   Boolean))
(define (empty-Prod? t s1 s2 N)
  (match t
    [(? Top?) (or (empty-Type? s1)
                  (empty-Type? s2)
                  (Prod-Phi s1 s2 N))]
    [(? Bot?) #t]
    [(Node _ (and p (Prod _ t1 t2)) l u r)
     (and (empty-Prod? l (And s1 t1) (And s2 t2) N)
          (empty-Prod? u s1 s2 N)
          (empty-Prod? r s1 s2 (cons p N)))]))

(: Prod-Phi (-> Type Type (Listof Prod) Boolean))
(define (Prod-Phi s1 s2 N)
  (match N
    [(cons (Prod _ t1 t2) N)
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
                       [(Arrow _ t1 t2)
                        (and (subtype? t1 dom)
                             (Arrow-Phi t1 (Not t2) P))])
                     N)]
    [(? Bot?) #t]
    [(Node _ (and a (Arrow _ s1 s2)) l u r)
     (and (empty-Arrow? l (Or s1 dom) (cons a P) N)
          (empty-Arrow? u dom P N)
          (empty-Arrow? r dom P (cons a N)))]))


(: Arrow-Phi (-> Type Type (Listof Arrow)
                 Boolean))
(define (Arrow-Phi t1 t2 P)
  (match P
    [(cons (Arrow _ s1* s2*) P)
     (let ([t1* (Diff t1 s1*)])
       (and (or (empty-Type? t1*)
                (let ([s2 (And* (map Arrow-rng P))])
                  (subtype? s2 (Not t2))))
            (Arrow-Phi t1 (And t2 s2*) P)
            (Arrow-Phi t1* t2 P)))]
    ;; this last clause was just #t from the paper...?
    [_ (or (empty-Type? t1)
           (empty-Type? t2))]))



(define Univ : Type (-type top-base top top))
(define Empty : Type  (-type bot-base bot bot))



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
