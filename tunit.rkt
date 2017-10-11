#lang typed/racket
(require (for-syntax racket/base
                     syntax/parse))

(provide check-equal?
         check-not-equal?
         check-eqv?
         check-not-eqv?
         check-eq?
         check-not-eq?
         check-true
         check-false
         check-not-false
         check-exn
         display-test-results)

;; To do:
;; 1) don't use printf, use exceptions
;; 2) write tests for these...
;; 3) tie these in to rackunit framework...?

(define passed-tests (make-parameter (box 0)))
(define failed-tests (make-parameter (box 0)))

(define-syntax-rule (with-fresh-test-count . bodies)
  (parameterize ([passed-tests (box 0)]
                 [failed-tests (box 0)])
    . bodies))

(define (test-passed!)
  (define b (passed-tests))
  (set-box! b (add1 (unbox b))))

(define (test-failed!)
  (define b (failed-tests))
  (set-box! b (add1 (unbox b))))

(define (display-test-results)
  (define passed (unbox (passed-tests)))
  (define total (+ passed (unbox (failed-tests))))
  (case total
    [(0) (void)]
    [(1) (if (= 1 passed)
           (printf "One test passed.\n")
           (printf "One test failed.\n"))]
    [(2) (if (= 1 passed)
           (printf "Two tests passed.\n")
           (printf "Two tests failed.\n"))]
    [else (printf "~a out of ~a tests passed.\n" passed total)]))

;; check-binary?
(define-syntax-rule (check-binary? orig-expr equality actual expected msg)
  (let ([a-val actual]
        [e-val expected])
    (cond
      [(not (equality a-val e-val))
       (test-failed!)
       (printf 
        "~a\nFAILURE\nexptected: ~a\nactual: ~a\nexpression: ~a\ncontext:\n  ~a:~a:~a\n~a~a\n" 
        "----------"
        e-val
        a-val
        orig-expr
        (syntax-source #'actual)
        (syntax-line #'actual)
        (syntax-column #'actual)
        (let ([message msg])
          (if message (string-append "Message: " message "\n") ""))
        "----------")]
      [else (test-passed!)])))

;; check-equal?
(define-syntax (check-equal? stx)
  (syntax-parse stx
    [(_ a b (~optional msg #:defaults ([msg #'#f])))
     #`(check-binary?
        '(check-equal? a b)
        equal?
        a
        b
        msg)]))

;; check-eqv?
(define-syntax (check-eqv? stx)
  (syntax-parse stx
    [(_ a b (~optional msg #:defaults ([msg #'#f])))
     #`(check-binary?
        '(check-eqv? a b)
        eqv?
        a
        b
        msg)]))

;; check-eq?
(define-syntax (check-eq? stx)
  (syntax-parse stx
    [(_ a b (~optional msg #:defaults ([msg #'#f])))
     #`(check-binary?
        '(check-eq? a b)
        eq?
        a
        b
        msg)]))

;; check-not-binary? (helper)
(define-syntax-rule (check-not-binary? orig-expr equality actual expected msg)
  (let ([a-val actual]
        [e-val expected])
    (cond
      [(equality a-val e-val)
       (test-failed!)
       (printf 
        "~a\nFAILURE\nexptected different values\nactual: ~a\nexpression: ~a\ncontext:\n  ~a:~a:~a\n~a~a\n" 
        "----------"
        a-val
        orig-expr
        (syntax-source #'actual)
        (syntax-line #'actual)
        (syntax-column #'actual)
        (let ([message msg])
          (if message (string-append "Message: " message "\n") ""))
        "----------")]
      [else (test-passed!)])))

;; check-not-equal?
(define-syntax (check-not-equal? stx)
  (syntax-parse stx
    [(_ a b (~optional msg #:defaults ([msg #'#f])))
     #`(check-not-binary?
        '(check-not-equal? a b)
        equal?
        a
        b
        msg)]))

;; check-not-eqv?
(define-syntax (check-not-eqv? stx)
  (syntax-parse stx
    [(_ a b (~optional msg #:defaults ([msg #'#f])))
     #`(check-not-binary?
        '(check-not-eqv? a b)
        eqv?
        a
        b
        msg)]))

;; check-not-eq?
(define-syntax (check-not-eq? stx)
  (syntax-parse stx
    [(_ a b (~optional msg #:defaults ([msg #'#f])))
     #`(check-not-binary?
        '(check-not-eq? a b)
        eq?
        a
        b
        msg)]))

;; check-false
(define-syntax (check-false stx)
  (syntax-parse stx
    [(_ actual (~optional msg #:defaults ([msg #'#f])))
     #'(let ([a-val actual])
         (cond
           [(not (equal? a-val #f))
            (test-failed!)
            (printf 
             "~a\nFAILURE\nexptected #f\nactual: ~a\nexpression: ~a\ncontext:\n  ~a:~a:~a\n~a~a\n" 
             "----------"
             a-val
             '(check-false actual)
             (syntax-source #'actual)
             (syntax-line #'actual)
             (syntax-column #'actual)
             (let ([message msg])
               (if message (string-append "Message: " message "\n") ""))
             "----------")]
           [else (test-passed!)]))]))


;; check-not-false
(define-syntax (check-not-false stx)
  (syntax-parse stx
    [(_ actual (~optional msg #:defaults ([msg #'#f])))
     #'(let ([a-val actual])
         (cond
           [(equal? a-val #f)
            (test-failed!)
            (printf 
             "~a\nFAILURE\nexptected non-#f value\nactual: ~a\nexpression: ~a\ncontext:\n  ~a:~a:~a\n~a~a\n" 
             "----------"
             a-val
             '(check-not-false actual)
             (syntax-source #'actual)
             (syntax-line #'actual)
             (syntax-column #'actual)
             (let ([message msg])
               (if message (string-append "Message: " message "\n") ""))
             "----------")]
           [else (test-passed!)]))]))

(define-syntax (check-true stx)
  (syntax-parse stx
    [(_ actual (~optional msg #:defaults ([msg #'#f])))
     #'(let ([a-val actual])
         (cond
           [(not (equal? #t a-val))
            (test-failed!)
            (printf 
             "~a\nFAILURE\nexptected: #t\nactual: ~a\nexpression: ~a\ncontext:\n  ~a:~a:~a\n~a~a\n" 
             "----------"
             a-val
             '(check-true actual)
             (syntax-source #'actual)
             (syntax-line #'actual)
             (syntax-column #'actual)
             (let ([message msg])
               (if message (string-append "Message: " message "\n") ""))
             "----------")]
           [else (test-passed!)]))]))


;; check-exn
(define-syntax (check-exn stx)
  (syntax-parse stx
    [(_ exn-pred thunk (~optional msg #:defaults ([msg #'#f])))
     #'(let ([a-val (with-handlers ([exn-pred (λ (_) (void))])
                      (thunk)
                      #f)])
         (cond
           [a-val
            (test-passed!)]
           [else
            (test-failed!)
            (printf 
             "~a\nFAILURE\nexptected exception\nactual: ~a\nexpression: ~a\ncontext:\n  ~a:~a:~a\n~a~a\n" 
             "----------"
             a-val
             '(check-exn exn-pred thunk)
             (syntax-source #'actual)
             (syntax-line #'actual)
             (syntax-column #'actual)
             (let ([message msg])
               (if message (string-append "Message: " message "\n") ""))
             "----------")]))]))