{-# OPTIONS --without-K #-}
-- NOTE: requires functional extensionality.
module Cats.Category.Sets.Facts.Exponential where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

open import Cats.Axioms using (funext)
open import Cats.Category
open import Cats.Category.Sets using (Sets)
open import Cats.Category.Sets.Facts.Product using (hasBinaryProducts)


instance
  hasExponentials : ∀ {l} → HasExponentials (Sets l)
  hasExponentials .HasExponentials.hasBinaryProducts = hasBinaryProducts
  hasExponentials .HasExponentials._↝′_ B C = record
    { Cᴮ = B → C
    ; eval = λ { (f , x) → f x }
    ; curry′ = λ f → record
      { arr = λ a b → f (a , b)
      ; prop = λ x → refl
      ; unique = λ eq a → funext λ b → sym (eq _)
      }
    }
