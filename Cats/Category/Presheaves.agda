{-# OPTIONS --without-K --safe #-}
module Cats.Category.Presheaves where

open import Level using (_⊔_ ; suc)

open import Cats.Category
open import Cats.Category.Fun using (Fun)
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Category.Setoids using (Setoids)


Presheaves : ∀ {lo la l≈} (C : Category lo la l≈) l l′
  → Category (lo ⊔ la ⊔ l≈ ⊔ suc (l ⊔ l′)) (lo ⊔ la ⊔ l ⊔ l′) (lo ⊔ l ⊔ l′)
Presheaves C l l′ = Fun (C ᵒᵖ) (Setoids l l′)
