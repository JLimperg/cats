module Cats.Category.Sets.Facts where

open import Cats.Category.Sets.Facts.Exponential public using (hasExponentials)
open import Cats.Category.Sets.Facts.Initial public using (hasInitial)
open import Cats.Category.Sets.Facts.Product public using
  (hasBinaryProducts ; hasFiniteProducts)
open import Cats.Category.Sets.Facts.Terminal public using (hasTerminal)

open import Cats.Category
open import Cats.Category.Sets using (Sets)


instance
  isCCC : ∀ {l} → IsCCC (Sets l)
  isCCC = record {}
