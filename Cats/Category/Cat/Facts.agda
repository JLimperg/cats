module Cats.Category.Cat.Facts where

open import Cats.Category.Cat.Facts.Initial public using (hasInitial)
open import Cats.Category.Cat.Facts.Terminal public using (hasTerminal)
open import Cats.Category.Cat.Facts.Product public using (hasBinaryProducts)
open import Cats.Category.Cat.Facts.Exponential public using (hasExponentials)

open import Cats.Category.Cat using (Cat)
open import Cats.Category.Constructions.Product using (HasFiniteProducts)
open import Cats.Category.Constructions.CCC using (IsCCC)


instance
  hasFiniteProducts : ∀ {lo la l≈} → HasFiniteProducts (Cat lo la l≈)
  hasFiniteProducts = record {}


  isCCC : ∀ {l} → IsCCC (Cat l l l)
  isCCC = record {}
