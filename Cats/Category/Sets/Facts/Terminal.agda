{-# OPTIONS --without-K #-}
module Cats.Category.Sets.Facts.Terminal where

open import Data.Unit using (⊤)
open import Level using (Lift ; lift ; lower)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Cats.Category
open import Cats.Category.Sets using (Sets)


instance
  hasTerminal : ∀ {l} → HasTerminal (Sets l)
  hasTerminal = record
    { ⊤ = Lift _ ⊤
    ; isTerminal = λ X → record { unique = λ _ _ → refl }
    }
