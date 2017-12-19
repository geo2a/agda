module Alga.API.Theorems where

open import Data.Char
open import Data.Empty
open import Agda.Builtin.Equality renaming (_≡_ to _===_)
open import Relation.Nullary

open import Alga.Algebra
open import Alga.Algebra.Theorems
open import Alga.API
open import Alga.Prelude
open import Alga.Reasoning
open import Alga.Algebra.Membership

-- vertices [x] == vertex x
vertices-vertex : ∀ {A} {x : A} -> vertices [ x ] ≡ vertex x
vertices-vertex = +identity >> reflexivity

-- edge x y == clique [x, y]
edge-clique : ∀ {A} {x y : A} -> edge x y ≡ clique (x :: [ y ])
edge-clique = symmetry (R *right-identity)

-- vertices xs ⊆ clique xs
vertices-clique : ∀ {A} {xs : List A} -> vertices xs ⊆ clique xs
vertices-clique {_} {[]}     = ⊆reflexivity
vertices-clique {a} {_ :: t} = ⊆transitivity (⊆right-monotony (vertices-clique {a} {t})) ⊆connect

-- clique (xs ++ ys) == connect (clique xs) (clique ys)
connect-clique : ∀ {A} {xs ys : List A} -> clique (xs ++ ys) ≡ connect (clique xs) (clique ys)
connect-clique {_} {[]}     = symmetry *left-identity
connect-clique {a} {_ :: t} = R (connect-clique {a} {t}) >> *associativity

-- hasVertex related lemmata
char-in-vertex : {c x : Char} -> (c === x) -> (c ∈ v x)
char-in-vertex refl = Here

char-not-in-vertex : {c x : Char} -> ¬(c === x) -> ¬(c ∈ v x)
char-not-in-vertex contra Here = contra refl

char-not-in-+ : {c : Char} {p q : Graph Char}-> ¬(c ∈ p) -> ¬(c ∈ q) -> ¬(c ∈ (p + q))
char-not-in-+ contra-p contra-q (There-+-left later) = contra-p later
char-not-in-+ contra-p contra-q (There-+-right later) = contra-q later

char-not-in-* : {c : Char} {p q : Graph Char}-> ¬(c ∈ p) -> ¬(c ∈ q) -> ¬(c ∈ (p * q))
char-not-in-* contra-p contra-q (There-*-left later) = contra-p later
char-not-in-* contra-p contra-q (There-*-right later) = contra-q later

-- Decide if a graph has a specific vertex
hasVertex : (x : Char) -> (g : Graph Char) -> Dec (x ∈ g)
hasVertex c ε = no (λ ())
hasVertex c (v x) with (c ≟ x) -- check if c is equal x
...             | (yes prf)    = yes (char-in-vertex prf)
...             | (no  contra) = no  (char-not-in-vertex contra)
hasVertex c (p + q) with hasVertex c p
...               | yes prf-p    = yes (There-+-left prf-p)
...               | no  contra-p with hasVertex c q
...                                 | yes prf-q    = yes (There-+-right prf-q)
...                                 | no  contra-q = no (char-not-in-+ contra-p contra-q)
hasVertex c (p * q) with hasVertex c p
...               | yes prf-p    = yes (There-*-left prf-p)
...               | no  contra-p with hasVertex c q
...                                 | yes prf-q    = yes (There-*-right prf-q)
...                                 | no  contra-q = no (char-not-in-* contra-p contra-q)

-- If graph has a vertex then singleton graph comprising this vertex is
-- a subgrah of the initial one
vertex-is-a-subgraph : ∀ {A} -> (x : A) -> (g : Graph A) -> (prf : x ∈ g) -> v x ⊆ g
vertex-is-a-subgraph x (v _) Here = +idempotence
vertex-is-a-subgraph x (p + q) (There-+-left prf) =
  begin
    v x + (p + q) ≡⟨ +associativity ⟩
    v x + p + q   ≡⟨ +left-congruence (vertex-is-a-subgraph x p prf) ⟩
    p + q
  ∎
vertex-is-a-subgraph x (p + q) (There-+-right prf) =
  begin
    v x + (p + q) ≡⟨ +associativity ⟩
    v x + p + q   ≡⟨ symmetry (transitivity +commutativity +associativity) ⟩
    p + q + v x   ≡⟨ symmetry +associativity ⟩
    p + (q + v x) ≡⟨ +right-congruence +commutativity ⟩
    p + (v x + q) ≡⟨ +right-congruence (vertex-is-a-subgraph x q prf) ⟩
    p + q
  ∎
vertex-is-a-subgraph x (p * q) (There-*-left prf) =
  begin
    v x + (p * q)                   ≡⟨ symmetry *left-identity ⟩
    ε * (v x + (p * q))             ≡⟨ left-distributivity ⟩
    ε * v x + ε * (p * q)           ≡⟨ +left-congruence *left-identity ⟩
    v x + ε * (p * q)               ≡⟨ +right-congruence *associativity ⟩
    v x + (ε * p * q)               ≡⟨ +right-congruence decomposition ⟩
    v x + (ε * p + ε * q + p * q)   ≡⟨ symmetry (+right-congruence +associativity) ⟩
    v x + (ε * p + (ε * q + p * q)) ≡⟨ +associativity ⟩
    v x + ε * p + (ε * q + p * q)   ≡⟨ +left-congruence (+right-congruence *left-identity) ⟩
    v x + p + (ε * q + p * q)       ≡⟨ +left-congruence (vertex-is-a-subgraph x p prf) ⟩
    -- woohoooo, recursiveee caaalll!!
    p + (ε * q + p * q)             ≡⟨ +associativity ⟩
    p + ε * q + p * q               ≡⟨ symmetry (+left-congruence (+left-congruence *left-identity)) ⟩
    ε * p + ε * q + p * q           ≡⟨ symmetry decomposition ⟩
    ε * p * q                       ≡⟨ *left-congruence *left-identity ⟩
    p * q
  ∎
vertex-is-a-subgraph x (p * q) (There-*-right prf) =
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
    v x + q + (p * q + ε * p)       ≡⟨ +left-congruence (vertex-is-a-subgraph x q prf) ⟩
    q + (p * q + ε * p)             ≡⟨ symmetry (+left-congruence *left-identity) ⟩
    ε * q + (p * q + ε * p)         ≡⟨ +right-congruence +commutativity ⟩
    ε * q + (ε * p + p * q)         ≡⟨ +associativity ⟩
    ε * q + ε * p + p * q           ≡⟨ +left-congruence +commutativity ⟩
    ε * p + ε * q + p * q           ≡⟨ symmetry decomposition ⟩
    ε * p * q                       ≡⟨ *left-congruence *left-identity ⟩
    p * q
  ∎
