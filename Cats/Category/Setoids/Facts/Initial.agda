{-# OPTIONS --without-K --safe #-}
module Cats.Category.Setoids.Facts.Initial where

open import Level
open import Relation.Binary using (Setoid)

open import Cats.Category
open import Cats.Category.Setoids using (Setoids ; ≈-intro)

import Data.Empty as Empty


⊥ : ∀ {l l′} → Setoid l l′
⊥ = record
  { Carrier = Lift _ Empty.⊥
  ; _≈_ = λ()
  ; isEquivalence = record
      { refl = λ{}
      ; sym = λ{}
      ; trans = λ{}
      }
  }


instance
  hasInitial : ∀ {l l≈} → HasInitial (Setoids l l≈)
  hasInitial = record
    { ⊥ = ⊥
    ; isInitial = λ X → record
      { arr = record { arr = λ() ; resp = λ{} }
      ; unique = λ _ → ≈-intro λ{}
      }
    }
