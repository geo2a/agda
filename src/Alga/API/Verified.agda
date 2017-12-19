module Alga.API.Verified where

open import Data.Char
open import Data.Empty
open import Agda.Builtin.Equality renaming (_≡_ to _===_)
open import Relation.Nullary

open import Alga.Algebra
open import Alga.API
open import Alga.Prelude
open import Alga.Reasoning
open import Alga.Algebra.Membership

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

-- hasVertex
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

-- removeVertex
--
removeVertex : (x : Char) -> (g : Graph Char) -> (x ∈ g) -> Graph Char
removeVertex x (v c) Here = ε
removeVertex x (p + q) (There-+-left  x-is-in-p) = ε -- removeVertex x p x-is-in-p + q
removeVertex x (p + q) (There-+-right x-is-in-q) = p + removeVertex x q x-is-in-q
removeVertex x (p * q) (There-*-left  x-is-in-p) = removeVertex x p x-is-in-p * q
removeVertex x (p * q) (There-*-right x-is-in-q) = p * removeVertex x q x-is-in-q
