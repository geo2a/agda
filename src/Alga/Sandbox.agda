module Alga.Sandbox where

open import Data.Char

open import Alga.Prelude
open import Alga.Algebra
open import Alga.Algebra.Membership
open import Alga.Algebra.Theorems
open import Alga.API
open import Alga.Reasoning

graphEx1 : Graph Char
graphEx1 = (v 'a' + v 'b') * (v 'c' + v 'd')

induced : Graph Char
induced = induce p graphEx1
  where
    p : Char -> Bool
    p 'a' = tt
    p 'b' = tt
    p  _  = ff
