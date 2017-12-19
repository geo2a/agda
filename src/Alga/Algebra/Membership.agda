module Alga.Algebra.Membership where

open import Alga.Prelude
open import Alga.Algebra

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
