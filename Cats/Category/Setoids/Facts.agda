module Cats.Category.Setoids.Facts where


open import Cats.Category.Setoids.Facts.Exponentials public using
  (hasExponentials)
open import Cats.Category.Setoids.Facts.Initial public using
  (hasInitial)
open import Cats.Category.Setoids.Facts.Products public using
  (hasProducts ; hasBinaryProducts ; hasFiniteProducts)
open import Cats.Category.Setoids.Facts.Terminal public using
  (hasTerminal)


open import Cats.Category
open import Cats.Category.Setoids using (Setoids)


instance
  isCCC : ∀ {l} → IsCCC (Setoids l l)
  isCCC = record {}
