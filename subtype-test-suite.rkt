#lang typed/racket/base

(require racket/match
         racket/list
         "tunit.rkt"
         "grammar.rkt")

(provide run-subtype-tests
         compare-subtype/random-types
         syntactic-subtype-timing)

(define Empty : TypeSexp 'Empty)
(define Univ : TypeSexp 'Univ)
(define Unit : TypeSexp 'Unit)
(define UnivProd : TypeSexp 'UnivProd)
(define UnivArrow : TypeSexp 'UnivArrow)
(define Int : TypeSexp 'Int)
(define Nat : TypeSexp 'Nat)
(define PosInt : TypeSexp 'PosInt)
(define NegInt : TypeSexp 'NegInt)
(define UInt8 : TypeSexp 'UInt8)
(define UInt16 : TypeSexp 'UInt16)
(define UInt32 : TypeSexp 'UInt32)
(define Int8 : TypeSexp 'Int8)
(define Int16 : TypeSexp 'Int16)
(define Int32 : TypeSexp 'Int32)
(define Bool : TypeSexp 'Bool)
(define Str : TypeSexp 'Str)
(define T : TypeSexp 'T)
(define F : TypeSexp 'F)

(: Prod (-> TypeSexp TypeSexp TypeSexp))
(define (Prod l r) `(Prod ,l ,r))

(: Arrow (-> TypeSexp TypeSexp TypeSexp))
(define (Arrow d r) `(Arrow ,d ,r))

(: And (-> TypeSexp * TypeSexp))
(define (And . ts)
  `(And . ,ts))

(: Or (-> TypeSexp * TypeSexp))
(define (Or . ts)
  `(Or . ,ts))

(: Not (-> TypeSexp TypeSexp))
(define (Not t)
  `(Not ,t))

(: random-type (-> Natural TypeSexp))
(define random-type
  (let ([base-types
         : (Vectorof TypeSexp)
         (vector-immutable Empty Univ Unit UnivProd UnivArrow Int Nat PosInt NegInt
                           UInt8 UInt16 UInt32 Int8 Int16 Int32 Bool Str T F)])
    (λ (fuel)
      (cond
        [(or (zero? fuel)
             (zero? (random (add1 fuel))))
         (vector-ref base-types (random (vector-length base-types)))]
        [else
         (let ([fuel (sub1 fuel)])
           (define ty (match (random 4)
                        [0 (Prod (random-type fuel) (random-type fuel))]
                        [1 (Arrow (random-type fuel) (random-type fuel))]
                        [2 (And (random-type fuel) (random-type fuel))]
                        [3 (Or (random-type fuel) (random-type fuel))]))
           (cond
             [(zero? (random 10)) (Not ty)]
             [else ty]))]))))

(: compare-subtype/random-types (All (X Y) (-> Natural
                                            (-> TypeSexp X)
                                            (-> X X Boolean)
                                            (-> TypeSexp Y)
                                            (-> Y Y Boolean)
                                            Void)))
(define (compare-subtype/random-types iters ->type1 subtype1? ->type2 subtype2?)
  (: run-test (-> Natural Void))
  (define (run-test fuel)
    (let* ([ty1 (random-type fuel)]
           [ty2 (random-type fuel)]
           [t11 (->type1 ty1)]
           [t12 (->type1 ty2)]
           [t21 (->type2 ty1)]
           [t22 (->type2 ty2)])
      (eprintf "type 1: ~a\n type 2: ~a\n" ty1 ty2)
      (collect-garbage)
      (collect-garbage)
      (collect-garbage)
      (eprintf "fuel: ~a, subtype1 (x10):\n" fuel)
      (define res1
        (time (for ([_ (in-range 9)])
                (subtype1? t12 t11)
                (subtype1? t12 t11))
              (cons (subtype1? t11 t12)
                    (subtype1? t12 t11))))
      (collect-garbage)
      (collect-garbage)
      (collect-garbage)
      (eprintf "fuel: ~a, subtype2 (x10):\n" fuel)
      (define res2
        (time (for ([_ (in-range 9)])
                (subtype2? t21 t22)
                (subtype2? t22 t21))
              (cons (subtype2? t21 t22)
                    (subtype2? t22 t21))))
      (unless (equal? res1 res2)
        (error 'compare-subtype-functions "Got ~a and ~a\n"
               res1 res2))))
  ;; run the rest 'iters' times
  (for ([i (in-range iters)])
    (run-test 3)
    (run-test 5)
    (run-test 8)
    (run-test 10)
    (eprintf "Finished iter ~a!\n" i))
  (printf "Finished comparing subtyping functions with ~a iterations.\n"  iters))

(: run-subtype-tests (All (X) (-> (-> TypeSexp X)
                                  (-> X X Boolean)
                                  Void)))
(define (run-subtype-tests ->X subtype-rel)
  (let ([subtype? (λ ([t1 : TypeSexp]
                      [t2 : TypeSexp])
                    (subtype-rel (->X t1) (->X t2)))])
    ;; basic
    (check-true  (subtype? Int Univ))
    (check-true  (subtype? (Not Int) (Not Nat)))
    (check-true  (subtype? (Not Int) (Not NegInt)))
    (check-false (subtype? (Not Nat) (Not Int)))
    (check-false (subtype? (Not NegInt) (Not Int)))
    (check-false (subtype? Univ Int))
    (check-true  (subtype? Empty Int))
    (check-true  (subtype? Empty Empty))
    (check-true  (subtype? (Not Empty) Univ))
    (check-false (subtype? Int Empty))
  
    ;; ranges
    (check-true  (subtype? Int8 Int8))
    (check-true  (subtype? PosInt Int))
    (check-true  (subtype? NegInt Int))
    (check-false (subtype? Int PosInt))
    (check-false (subtype? Int NegInt))
    (check-false (subtype? PosInt NegInt))
    (check-false (subtype? NegInt PosInt))
    (check-false (subtype? Int16 Int8))
    (check-false (subtype? Int32 Int8))
    (check-false (subtype? Int32 Int16))
    (check-true  (subtype? PosInt Nat))
    (check-true  (subtype? PosInt Nat))
    (check-true  (subtype? UInt8 UInt16))
    (check-true  (subtype? UInt8 Int16))
    (check-true  (subtype? Int16 Int32))
  
    ;; unions
    (check-true  (subtype? (Or NegInt PosInt) Int))
    (check-true  (subtype? (Or NegInt Nat) Int))
    (check-false (subtype? Int (Or NegInt PosInt)))
    (check-true  (subtype? Int (Or NegInt Nat)))
    (check-true  (subtype? Int (Or Int Unit)))
    (check-true  (subtype? Int (Or Int Bool)))
    (check-true  (subtype? Bool (Or Int Bool)))
    (check-true  (subtype? Empty (Or Int Bool)))
    (check-true  (subtype? Bool (Or Empty Bool)))
    (check-false (subtype? (Or Int Unit) Int))
    (check-false (subtype? Bool Int))
    (check-false (subtype? Int Bool))
    (check-false (subtype? Bool (Or Empty T Int32)))
    (check-false (subtype? (Or Int Bool) Empty))
  
    ;; intersections
    (check-true  (subtype? (And Int8 Int16) Int32))
    (check-true  (subtype? (And Int32 Int16) Int32))
    (check-true  (subtype? (And Int8 Int16) (And Int8 Int32)))
    (check-true  (subtype? (And UInt8 UInt16) (And Int16 Int32)))
    (check-true  (subtype? (And UInt8 Int16) (Or Int16 Int32)))
    (check-false (subtype? Int16 (And UInt8 Int16)))
    (check-true  (subtype? (And UInt8 Int16) Int16))
    (check-false  (subtype? Int8 (And UInt8 Int16)))
    (check-false  (subtype? (And UInt8 Int16) Int8))
    (check-false (subtype? Int32 (And UInt8 Int16)))
    (check-false (subtype? (Or Int16 Int32) (And UInt8 Int16)))
    (check-true  (subtype? (And Int Unit) Int))
    (check-true  (subtype? (And Int Unit (Not Univ)) Int))
    (check-true  (subtype? (And Int Bool (Not Bool)) Int))
    (check-true  (subtype? (And Int (Not NegInt)) Nat))
    (check-true  (subtype? Nat (And Int (Not NegInt))))
    (check-false (subtype? (And Int (Not PosInt)) NegInt))
    (check-true  (subtype? (And Int (Not Nat)) NegInt))
    (check-true  (subtype? NegInt (And Int (Not PosInt))))
    (check-true  (subtype? (And Int Unit) Int))
    (check-false (subtype? Int (And Int Unit)))
    (check-true  (subtype? (And (Or Int Unit)
                                (Or Int Bool))
                           Int))
    (check-true  (subtype? Int
                           (And (Or Int Unit)
                                (Or Int Bool))))
    (check-true  (subtype? (And Int Bool) Empty))
    (check-true  (subtype? Empty (And Int Bool)))
  
    ;; products
    (check-true  (subtype? (Prod Int Int) (Prod Univ Univ)))
    (check-true  (subtype? (Prod Empty Int) (Prod Int Int)))
    (check-true  (subtype? (Prod Int Empty) (Prod Int Int)))
    (check-true  (subtype? (Prod Int Int) (Prod Int Univ)))
    (check-true  (subtype? (Prod Int Int) (Prod Univ Int)))
    (check-true  (subtype? (Prod Int Int) (Prod Int Int)))
    (check-false (subtype? (Prod Int Int) (Prod Empty Int)))
    (check-false (subtype? (Prod Int Int) (Prod Int Empty)))
    (check-false (subtype? (Prod Int Int) (Prod Empty Empty)))
    (check-false (subtype? (Prod Int Int) (Prod Bool Int)))
    (check-false (subtype? (Prod Int Int) (Prod Int Bool)))
    (check-true  (subtype? (Prod Int Int) (Prod (Or Int Bool) Int)))
    (check-true  (subtype? (Prod Int Int) (Prod Int (Or Int Bool))))
    (check-false  (subtype? (Or (Prod Int Int)
                                (Prod Str Str))
                            Empty))
    (check-true  (subtype? (And (Prod Int Int)
                                (Prod Str Str))
                           Empty))
    (check-true  (subtype? (And (Prod (Or Int Str) (Or Int Str))
                                (Prod (Or Int Unit) (Or Int Unit)))
                           (Prod Int Int)))
    (check-true  (subtype? (Prod Int Int)
                           (And (Prod (Or Int Str) (Or Int Str))
                                (Prod (Or Int Unit) (Or Int Unit)))))
    (check-false (subtype? (Prod (Or Int Bool) Int)
                           (Prod Int Int)))
    (check-false (subtype? (Prod Int (Or Int Bool))
                           (Prod Int Int)))
    (check-true  (subtype? (And (Prod Univ Int)
                                (Prod Int Univ))
                           (Prod Int Int)))
    (check-true  (subtype? (Prod Int Int)
                           (And (Prod Univ Int)
                                (Prod Int Univ))))
    (check-true  (subtype? (Prod Int Int)
                           (And (Prod (Or Bool Int) Int)
                                (Prod (Not Bool) (Or Bool Int)))))
    (check-true  (subtype? (Prod Int Int)
                           (And (Prod Univ Int)
                                (Prod Int Univ))))
    (check-false (subtype? (Prod (Or Int Bool)
                                 (Or Int Bool))
                           (Or (Prod Int Bool)
                               (Prod Bool Int))))
    (check-true (subtype? (Or (Prod Int Bool)
                              (Prod Bool Int))
                          (Prod (Or Int Bool)
                                (Or Int Bool))))
    (check-true (subtype? (Prod (Prod (Or Int Bool)
                                      (Or Int Bool))
                                (Prod (Or Int Bool)
                                      (Or Int Bool)))
                          (Prod (Or (Prod Int Int)
                                    (Prod Bool Int)
                                    (Prod Int Bool)
                                    (Prod Bool Bool))
                                (Or (Prod Int Int)
                                    (Prod Bool Int)
                                    (Prod Int Bool)
                                    (Prod Bool Bool)))))
  
    ;; arrows
    (check-false (subtype? (Arrow Empty Empty) Empty))
    (check-true (subtype? (Arrow Empty Empty) Univ))
    (check-true  (subtype? (Arrow Empty Univ) (Arrow Empty Empty)))
    (check-false (subtype? (Arrow Empty Univ) (Arrow Univ Empty)))
    (check-true  (subtype? (Arrow Int Int) (Arrow Int Univ)))
    (check-true  (subtype? (Arrow Univ Int) (Arrow Int Univ)))
    (check-false (subtype? (Arrow Int Int) (Arrow Univ Int)))
    (check-false (subtype? (Arrow Int Univ) (Arrow Int Int)))
    (check-true  (subtype? (And (Arrow NegInt NegInt)
                                (Arrow Nat    Nat))
                           (Arrow Int Int)))
    (check-false  (subtype? (Arrow Int Int)
                            (And (Arrow NegInt NegInt)
                                 (Arrow Nat    Nat))))
    (check-false  (subtype? (Or (Arrow NegInt NegInt)
                                (Arrow Nat    Nat))
                            (And (Arrow NegInt NegInt)
                                 (Arrow Nat    Nat))))
    (check-true  (subtype? (And (Arrow NegInt NegInt)
                                (Arrow Nat    Nat))
                           (Or (Arrow NegInt NegInt)
                               (Arrow Nat    Nat))))
    (check-true  (subtype? (And (Arrow (Prod NegInt Univ) NegInt)
                                (Arrow (Prod Univ NegInt) NegInt)
                                (Arrow (Prod Nat Univ) Nat)
                                (Arrow (Prod Univ Nat) Nat))
                           (And (Arrow (Prod NegInt NegInt) NegInt)
                                (Arrow (Prod Nat Nat) Nat)
                                (Arrow (Prod Int Int) Int))))
    (check-false  (subtype? (And (Arrow (Or (Prod NegInt Univ)
                                            (Prod Univ NegInt)
                                            (Prod Nat Univ)
                                            (Prod Univ Nat))
                                        (Or NegInt Nat)))
                            (And (Arrow (Prod NegInt NegInt) NegInt)
                                 (Arrow (Prod Nat Nat) Nat)
                                 (Arrow (Prod Int Int) Int))))
    (check-true  (subtype? (And (Arrow Bool Bool)
                                (Arrow (Prod Bool Bool) Str)
                                (Arrow (Arrow Bool Bool) Unit)
                                (Arrow Nat (Prod Univ Nat)))
                           (Arrow (Or Bool
                                      (Prod Bool Bool)
                                      (Arrow Bool Bool)
                                      Nat)
                                  Univ)))
    (check-false  (subtype? (And (Arrow Bool Bool)
                                 (Arrow (Prod Bool Bool) Str)
                                 (Arrow (Arrow Bool Bool) Unit)
                                 (Arrow Nat (Prod Univ Nat)))
                            (Arrow Univ Univ)))

    ;; misc
    (check-true (subtype? (Or (Prod (Prod (Or (Prod Int16 Unit) UnivArrow) Empty)
                                    UnivArrow)
                              (And (Arrow NegInt (Or Int32 Int32)) NegInt))
                          T))

    (display-test-results)))



(: syntactic-subtype-timing (All (X Y) (-> (-> TypeSexp X)
                                           (-> X X Boolean)
                                           (-> TypeSexp Y)
                                           (-> Y Y Boolean)
                                           Void)))
(define (syntactic-subtype-timing ->type1 subtype1?
                                  ->type2 subtype2?)
  (: single-test (-> Natural
                     Symbol
                     (Listof (List TypeSexp TypeSexp))
                     Void))
  (define (single-test iters test-name types)
    (define lhs (map (ann first  (-> (List TypeSexp TypeSexp) TypeSexp)) types))
    (define rhs (map (ann second (-> (List TypeSexp TypeSexp) TypeSexp)) types))
    (eprintf "test:~a:1 (~a iterations)\n" test-name iters)
    (define res1
      (let ([ls (map ->type1 lhs)]
            [rs (map ->type1 rhs)])
        (collect-garbage)
        (collect-garbage)
        (collect-garbage)
        (time (for ([_ (in-range iters)])
                (for ([l (in-list ls)]
                      [r (in-list rs)])
                  (subtype1? l r)))
              (map subtype1? ls rs))))
    (eprintf "test:~a:2 (~a iterations)\n" test-name iters)
    (define res2
      (let ([ls (map ->type2 lhs)]
            [rs (map ->type2 rhs)])
        (collect-garbage)
        (collect-garbage)
        (collect-garbage)
        (time (for ([_ (in-range iters)])
                (for ([l (in-list ls)]
                      [r (in-list rs)])
                  (subtype2? l r)))
              (map subtype2? ls rs))))
    (unless (equal? res1 res2)
      (error 'single-test "got ~a/~a with input ~a\n"
             res1 res2 types)))


  (single-test 10000
               'atoms
               '([Int Int]
                 [Int Str]
                 [Empty Str]
                 [Str Empty]
                 [Int Univ]
                 [Univ Int]))


  (single-test 1000
               'unions-subset
               '([(Or Unit Str)
                  (Or Unit Str Bool)]
                 [(Or Str Bool (Prod Unit Unit))
                  (Or Str Bool Unit (Prod Unit Unit) (Prod Str Str))]
                 [(Or Int Str Bool (Prod Int Int) (Prod Str Str) (Prod Unit Unit))
                  (Or Int Str Bool Unit (Prod Int Int) (Prod Str Str))]
                 [(Or Int Str Bool
                      (Prod Int Int)
                      (Prod Str Str)
                      (Prod Unit Unit)
                      (Arrow Str Str))
                  (Or Int Str Bool Unit
                      (Prod Int Int)
                      (Prod Str Str)
                      (Prod Unit Unit)
                      (Prod Bool Bool)
                      (Arrow Str Str)
                      (Arrow Bool Bool))]))


  (single-test 1000
               'unions-subtype
               '([(Or (Prod T F) (Arrow T F))
                  (Or (Prod Bool Bool) (Arrow Bool Bool))]
                 [(Or (Prod T F) (Prod F T) (Arrow T F) (Arrow F T))
                  (Or (Prod Bool Bool) (Arrow Bool Bool))]
                 [(Or (Prod T F) (Prod F T) (Arrow T F) (Arrow F T)
                      (Prod Bool Bool) (Arrow Bool Bool))
                  (Or (Prod (Or Unit Bool)
                            (Or Unit Bool))
                      (Arrow (Or Unit Bool)
                             (Or Unit Bool)))]
                 [(Or (Prod T F) (Prod F T) (Arrow T F) (Arrow F T)
                      (Prod Bool Bool)
                      (Arrow Bool Bool)
                      (Prod (Prod T F) (Prod T F)))
                  (Or (Prod (Or Unit Bool)
                            (Or Unit Bool))
                      (Prod (Prod (Or Unit Bool)
                                  (Or Unit Bool))
                            (Prod (Or Unit Bool)
                                  (Or Unit Bool)))
                      (Prod Int Int)
                      (Prod Str Str)
                      (Arrow (Or Unit Bool)
                             (Or Unit Bool))
                      (Arrow Int Int))]
                 [(Or (Prod T F) (Prod F T) (Arrow T F) (Arrow F T)
                      (Prod Bool Bool)
                      (Arrow Bool Bool)
                      (Prod (Prod (Prod T F)
                                  (Prod T F))
                            (Prod (Prod T F)
                                  (Prod T F))))
                  (Or (Prod (Or Unit Bool)
                            (Or Unit Bool))
                      (Prod (Prod (Or Unit Bool)
                                  (Or Unit Bool))
                            (Prod (Or Unit Bool)
                                  (Or Unit Bool)))
                      (Prod Int Int)
                      (Prod Str Str)
                      (Arrow (Or Unit Bool)
                             (Or Unit Bool))
                      (Arrow Int Int))])))




;;; a disjoint Union of size 16
;(define SomeBase (Or (set 'True
;                          'False
;                          'String
;                          'Symbol
;                          Int8
;                          Int16
;                          (Arrow Int8 Int8)
;                          (Arrow Int16 Int16))))
;
;;; the powerset of the elements of SomeBase
;(define 2^SomeBase : (Listof (Or Type))
;  (map (inst Or Type) (subsets (Or-ts SomeBase))))
;
;;; The supertype of any product of SomeBase types
;(define UnivBaseProd (Prod SomeBase SomeBase))
;
;;; the cartesian product of SomeBase
;;; i.e. all products t1 × t2 where t1,t2 ∈ SomeBase
;(define SomeBase×SomeBase
;  (for*/list : (Setof Type)
;    ([t1 (in-set (Or-ts SomeBase))]
;     [t2 (in-set (Or-ts SomeBase))])
;    (Prod t1 t2)))
;
;;; the cartesian product of SomeBase
;;; i.e. all products t1 × t2 where t1,t2 ∈ SomeBase
;(define SomeBase→SomeBase
;  (for*/list : (Setof Type)
;    ([t1 (in-set (Or-ts SomeBase))]
;     [t2 (in-set (Or-ts SomeBase))])
;    (Prod t1 t2)))
;
;(define misc-prods (set UnivBaseProd
;                        (Prod 'Symbol (Or (set Int8 'Symbol)))
;                        (Prod (Or (set 'Symbol Bool)) Int8)
;                        (Prod (Or (set 'Symbol Int16))
;                              Int8)
;                        (Prod Int8
;                              (Or (set 'Symbol Int16)))
;                        (Prod (Arrow Int8 Int8)
;                              (Arrow Int8 Int8))))
;(define 2^misc-prods (map (inst Or Type) (subsets misc-prods)))
;
;(define misc-arrows (set UnivArrow
;                         (Arrow 'Symbol (Or (set Int8 'Symbol)))
;                         (Arrow (Or (set 'Symbol Bool)) Int8)
;                         (Arrow (Or (set 'Symbol Int16))
;                                Int8)
;                         (Arrow Int8
;                                (Or (set 'Symbol Int16)))
;                         (Arrow (Arrow Int8 Int8)
;                                (Arrow Int8 Int8))))
;(define 2^misc-arrows (map (inst Or Type) (subsets misc-prods)))
;
;
;(: ->nat (-> Boolean Natural))
;(define (->nat b) (if b 1 0))
;
;(: run-subtype-benchmark (-> String (-> Type Type Boolean) Void))
;(define (run-subtype-benchmark name subtype?)
;  (collect-garbage)
;  (collect-garbage)
;  (collect-garbage)
;  (printf "~a: simple unions (size <= 8)\n" name)
;  (printf "[nat result ~a]\n"
;          (time (for*/sum : Natural
;                  ([disj1 (in-list 2^SomeBase)]
;                   [disj2 (in-list 2^SomeBase)])
;                  (+ (->nat (subtype? disj1 disj2))
;                     (->nat (subtype? disj2 disj1))))))
;
;  (collect-garbage)
;  (collect-garbage)
;  (collect-garbage)
;  (printf "~a: products of simple types\n" name)
;  (printf "[nat result ~a]\n"
;          (time (for*/sum : Natural
;                  ([prod1 (in-list SomeBase×SomeBase)]
;                   [prod2 (in-list SomeBase×SomeBase)])
;                  (+ (->nat (subtype? prod1 prod2))
;                     (->nat (subtype? prod2 prod1))))))
;
;  (collect-garbage)
;  (collect-garbage)
;  (collect-garbage)
;  (printf "~a: products of unions (size <= 8)\n" name)
;  (printf "[nat result ~a]\n"
;          (time (for*/sum : Natural
;                  ([t1 (in-list 2^SomeBase)]
;                   [t2 (in-list 2^SomeBase)])
;                  (+ (->nat (subtype? (Prod t1 t2) (Prod t2 t1)))
;                     (->nat (subtype? (Prod t1 t2) (Prod t2 t1)))
;                     (->nat (subtype? (Prod t1 t2) UnivBaseProd))
;                     (->nat (subtype? UnivBaseProd (Prod t1 t2)))))))
;
;  (collect-garbage)
;  (collect-garbage)
;  (collect-garbage)
;  (printf "~a: unions of products of unions (misc)\n" name)
;  (printf "[nat result ~a]\n"
;          (time (for*/sum : Natural
;                  ([t1 (in-list 2^misc-prods)]
;                   [t2 (in-list 2^misc-prods)])
;                  (+ (->nat (subtype? t1 t2))
;                     (->nat (subtype? t2 t1))))))
;
;  (collect-garbage)
;  (collect-garbage)
;  (collect-garbage)
;  (printf "~a: arrows of simple types\n" name)
;  (printf "[nat result ~a]\n"
;          (time (for*/sum : Natural
;                  ([arrow1 (in-list SomeBase→SomeBase)]
;                   [arrow2 (in-list SomeBase→SomeBase)])
;                  (+ (->nat (subtype? arrow1 arrow2))
;                     (->nat (subtype? arrow2 arrow1))))))
;
;  (collect-garbage)
;  (collect-garbage)
;  (collect-garbage)
;  (printf "~a: arrows of unions (size <= 8)\n" name)
;  (printf "[nat result ~a]\n"
;          (time (for*/sum : Natural
;                  ([t1 (in-list 2^SomeBase)]
;                   [t2 (in-list 2^SomeBase)])
;                  (+ (->nat (subtype? (Arrow t1 t2) (Arrow t2 t1)))
;                     (->nat (subtype? (Arrow t1 t2) (Arrow t2 t1)))
;                     (->nat (subtype? (Arrow t1 t2) UnivArrow))
;                     (->nat (subtype? UnivArrow (Arrow t1 t2)))))))
;
;  (collect-garbage)
;  (collect-garbage)
;  (collect-garbage)
;  (printf "~a: unions of Arrows of unions (misc)\n" name)
;  (printf "[nat result ~a]\n"
;          (time (for*/sum : Natural
;                  ([t1 (in-list 2^misc-arrows)]
;                   [t2 (in-list 2^misc-arrows)])
;                  (+ (->nat (subtype? t1 t2))
;                     (->nat (subtype? t2 t1))))))
;  )
