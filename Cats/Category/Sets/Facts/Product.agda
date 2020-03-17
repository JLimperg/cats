{-# OPTIONS --without-K --safe #-}
module Cats.Category.Sets.Facts.Product where

open import Data.Bool using (Bool ; true ; false)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong₂)

open import Cats.Category
open import Cats.Category.Sets using (Sets)

import Cats.Category.Sets.Facts.Terminal


instance
  hasBinaryProducts : ∀ {l} → HasBinaryProducts (Sets l)
  hasBinaryProducts .HasBinaryProducts._×′_ A B = record
    { prod = A × B
    ; proj = λ where
        true → proj₁
        false → proj₂
    ; isProduct = λ p → record
        { arr = λ x → p true x , p false x
        ; prop = λ where
            true → λ _ → refl
            false → λ _ → refl
        ; unique = λ eq x → cong₂ _,_ (eq true x) (eq false x)
        }
    }


  hasFiniteProducts :  ∀ {l} → HasFiniteProducts (Sets l)
  hasFiniteProducts = record {}
