{-# OPTIONS --without-K --safe #-}
module Cats.Category.Setoids.Facts.Terminal where

open import Level
open import Relation.Binary using (Setoid)

open import Cats.Category
open import Cats.Category.Setoids using (Setoids)

import Data.Unit as Unit


⊤ : ∀ {l l′} → Setoid l l′
⊤ = record
  { Carrier = Lift _ Unit.⊤
  ; _≈_ = λ _ _ → Lift _ Unit.⊤
  }


instance
  hasTerminal : ∀ {l l≈} → HasTerminal (Setoids l l≈)
  hasTerminal = record { ⊤ = ⊤ }
