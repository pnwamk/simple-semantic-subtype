#lang typed/racket/base

(provide (all-defined-out))

(define-type TypeSexp
  (Rec x (U 'Univ
            'Empty
            'Unit
            'Bool
            'Str
            'UnivProd
            'UnivArrow
            'Int
            'T
            'F
            'Nat
            'PosInt
            'NegInt
            'UInt8
            'UInt16
            'UInt32
            'Int8
            'Int16
            'Int32
            (List 'Prod x x)
            (List 'Arrow x x)
            (Pair 'Or (Listof x))
            (Pair 'And (Listof x))
            (List 'Not x))))
