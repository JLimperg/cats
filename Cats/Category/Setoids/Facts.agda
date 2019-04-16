module Cats.Category.Setoids.Facts where


open import Cats.Category
open import Cats.Category.Setoids using (Setoids)
open import Cats.Category.Setoids.Facts.Exponentials using (hasExponentials)
open import Cats.Category.Setoids.Facts.Initial using (hasInitial)
open import Cats.Category.Setoids.Facts.Products
  using (hasProducts ; hasBinaryProducts)
open import Cats.Category.Setoids.Facts.Terminal using (hasTerminal)


instance
  -- TODO move to Cats.Category.Setoids.Facts.Products
  hasFiniteProducts : ∀ {l l≈} → HasFiniteProducts (Setoids l l≈)
  hasFiniteProducts = record {}

  isCCC : ∀ {l} → IsCCC (Setoids l l)
  isCCC = record {}
