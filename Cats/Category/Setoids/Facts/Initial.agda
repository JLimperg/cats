module Cats.Category.Setoids.Facts.Initial where

open import Data.Empty using (⊥)
open import Level

open import Cats.Category
open import Cats.Category.Setoids using (Setoids ; ≈-intro)


module Build {l} {l≈} where

  open Category (Setoids l l≈)


  Zero : Obj
  Zero = record
      { Carrier = Lift l ⊥
      ; _≈_ = λ()
      ; isEquivalence = record
          { refl = λ{}
          ; sym = λ{}
          ; trans = λ{}
          }
      }


  isInitial : IsInitial Zero
  isInitial X = ∃!-intro
      (record { arr = λ() ; resp = λ{} })
      _
      λ _ → ≈-intro λ {}


open Build


instance
  hasInitial : ∀ {l l≈} → HasInitial (Setoids l l≈)
  hasInitial = record
      { Zero = Zero
      ; isInitial = isInitial
      }
