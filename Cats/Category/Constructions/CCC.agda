{-# OPTIONS --without-K --safe #-}
module Cats.Category.Constructions.CCC where

open import Level

open import Cats.Category.Base
open import Cats.Category.Constructions.Exponential using
  (HasExponentials)
open import Cats.Category.Constructions.Product using
  (HasFiniteProducts)


record IsCCC {lo la l≈} (Cat : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈) where
  field
    {{hasFiniteProducts}} : HasFiniteProducts Cat
    {{hasExponentials}} : HasExponentials Cat
