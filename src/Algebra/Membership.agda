module Algebra.Membership where

open import Prelude
open import Algebra

data _∈_ {A : Set} : A -> Graph A -> Set where
     Here : {x : A} -> x ∈ (v x)
     There-+-left  : {x : A} -> {p : Graph A} -> {q : Graph A} ->
                     (later : x ∈ p) -> x ∈ (p + q)
     There-+-right : {x : A} -> {p : Graph A} -> {q : Graph A} ->
                     (later : x ∈ q) -> x ∈ (p + q)
     There-*-left : {x : A} -> {p : Graph A} -> {q : Graph A} ->
                    (later : x ∈ p) -> x ∈ (p * q)
     There-*-right : {x : A} -> {p : Graph A} -> {q : Graph A} ->
                    (later : x ∈ q) -> x ∈ (p * q)

-- Nothing can be in an empty graph
ε-has-nothing : {A : Set} -> {x : A} -> ¬ (x ∈ ε)
ε-has-nothing ()

g1 : Graph ℕ
g1 = (v zero) * (v (suc (suc zero))) + (v (suc zero))

p-g1 : zero ∈ g1
p-g1 = There-+-left (There-*-left Here)
