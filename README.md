# simple-semantic-subtype

This repo contains several approaches to representing the types defined
in `type-grammar.rkt` and calculating subtyping queries for those types.

The general approaches to the semantic subtyping strategies used herein
were written after studying section 4 of unpublished manuscript 
"Covariance and Contravariance: a fresh look at an old issue" 
by Giuseppe Castagna and after looking a little at the OCaml 
implementation of [CDuce](http://www.cduce.org/).

Many thanks to Castagna et al. for their work in designing and clearly 
describing these algorithms over the course of their work.


The types follow the following grammar:

```
;; TypeSexp ::= Univ
;;            | Empty
;;            | Unit
;;            | Bool
;;            | Str
;;            | UnivProd
;;            | UnivArrow
;;            | Int
;;            | T
;;            | F
;;            | Nat
;;            | PosInt
;;            | NegInt
;;            | UInt8
;;            | UInt16
;;            | UInt32
;;            | Int8
;;            | Int16
;;            | Int32
;;            | (Prod TypeSexp TypeSexp)
;;            | (Arrow TypeSexp TypeSexp)
;;            | (Or TypeSexp ...)
;;            | (And TypeSexp ...)
;;            | (Not TypeSexp)
```
