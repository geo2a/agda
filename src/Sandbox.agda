module Sandbox where

open import Agda.Builtin.Char
open import Prelude
open import Algebra
open import Algebra.Membership
open import Algebra.Theorems
open import API
open import Reasoning

graphEx1 : Graph Char
graphEx1 = (v 'a' + v 'b') * (v 'c' + v 'd')

induced : Graph Char
induced = induce p graphEx1
  where
    p : Char -> Bool
    p 'a' = tt
    p 'b' = tt
    p  _  = ff

hasVertex-works : ∀ {A} -> (x : A) -> (g : Graph A) -> (prf : x ∈ g) -> v x ⊆ g
hasVertex-works x (v _) Here = +idempotence
hasVertex-works x (p + q) (There-+-left prf) =
  begin
    v x + (p + q) ≡⟨ +associativity ⟩
    v x + p + q   ≡⟨ +left-congruence (hasVertex-works x p prf) ⟩
    p + q
  ∎
hasVertex-works x (p + q) (There-+-right prf) =
  begin
    v x + (p + q) ≡⟨ +associativity ⟩
    v x + p + q   ≡⟨ symmetry (transitivity +commutativity +associativity) ⟩
    p + q + v x   ≡⟨ symmetry +associativity ⟩
    p + (q + v x) ≡⟨ +right-congruence +commutativity ⟩
    p + (v x + q) ≡⟨ +right-congruence (hasVertex-works x q prf) ⟩
    p + q
  ∎
hasVertex-works x (p * q) (There-*-left prf) =
  begin
    v x + (p * q)                   ≡⟨ symmetry *left-identity ⟩
    ε * (v x + (p * q))             ≡⟨ left-distributivity ⟩
    ε * v x + ε * (p * q)           ≡⟨ +left-congruence *left-identity ⟩
    v x + ε * (p * q)               ≡⟨ +right-congruence *associativity ⟩
    v x + (ε * p * q)               ≡⟨ +right-congruence decomposition ⟩
    v x + (ε * p + ε * q + p * q)   ≡⟨ symmetry (+right-congruence +associativity) ⟩
    v x + (ε * p + (ε * q + p * q)) ≡⟨ +associativity ⟩
    v x + ε * p + (ε * q + p * q)   ≡⟨ +left-congruence (+right-congruence *left-identity) ⟩
    v x + p + (ε * q + p * q)       ≡⟨ +left-congruence (hasVertex-works x p prf) ⟩
    -- woohoooo, recursiveee caaalll!!
    p + (ε * q + p * q)             ≡⟨ +associativity ⟩
    p + ε * q + p * q               ≡⟨ symmetry (+left-congruence (+left-congruence *left-identity)) ⟩
    ε * p + ε * q + p * q           ≡⟨ symmetry decomposition ⟩
    ε * p * q                       ≡⟨ *left-congruence *left-identity ⟩
    p * q
  ∎
hasVertex-works x (p * q) (There-*-right prf) =
  begin
    v x + (p * q)                   ≡⟨ symmetry *left-identity ⟩
    ε * (v x + (p * q))             ≡⟨ left-distributivity ⟩
    ε * v x + ε * (p * q)           ≡⟨ +left-congruence *left-identity ⟩
    v x + ε * (p * q)               ≡⟨ +right-congruence *associativity ⟩
    v x + (ε * p * q)               ≡⟨ +right-congruence decomposition ⟩
    v x + (ε * p + ε * q + p * q)   ≡⟨ symmetry (+right-congruence +associativity) ⟩
    v x + (ε * p + (ε * q + p * q)) ≡⟨ +right-congruence +commutativity ⟩
    v x + ((ε * q + p * q) + ε * p) ≡⟨ symmetry (+right-congruence +associativity) ⟩
    v x + (ε * q + (p * q + ε * p)) ≡⟨ +associativity ⟩
    v x + ε * q + (p * q + ε * p)   ≡⟨ +left-congruence (+right-congruence *left-identity) ⟩
    v x + q + (p * q + ε * p)       ≡⟨ +left-congruence (hasVertex-works x q prf) ⟩
    q + (p * q + ε * p)             ≡⟨ symmetry (+left-congruence *left-identity) ⟩
    ε * q + (p * q + ε * p)         ≡⟨ +right-congruence +commutativity ⟩
    ε * q + (ε * p + p * q)         ≡⟨ +associativity ⟩
    ε * q + ε * p + p * q           ≡⟨ +left-congruence +commutativity ⟩
    ε * p + ε * q + p * q           ≡⟨ symmetry decomposition ⟩
    ε * p * q                       ≡⟨ *left-congruence *left-identity ⟩
    p * q
  ∎
