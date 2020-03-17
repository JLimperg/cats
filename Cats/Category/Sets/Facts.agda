{-# OPTIONS --without-K --safe #-}
open import Axiom.Extensionality.Propositional using (Extensionality)

module Cats.Category.Sets.Facts
  (funext : ∀ {a b} → Extensionality a b)
  where

open import Cats.Category.Sets.Facts.Exponential funext public using (hasExponentials)
open import Cats.Category.Sets.Facts.Initial public using (hasInitial)
open import Cats.Category.Sets.Facts.Product public using
  (hasBinaryProducts ; hasFiniteProducts)
open import Cats.Category.Sets.Facts.Terminal public using (hasTerminal)

open import Cats.Category
open import Cats.Category.Sets using (Sets)


instance
  isCCC : ∀ {l} → IsCCC (Sets l)
  isCCC = record {}
