module Cats.Category.Setoids.Facts.Initial where

open import Data.Empty using (⊥)
open import Level

open import Cats.Category
open import Cats.Category.Setoids using (Setoids)


module Build {l} {l≈} where

  open Category (Setoids l l≈)


  Zero : Obj
  Zero = record
      { Carrier = Lift ⊥
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
      (λ _ {})


open Build


instance
  hasInitial : ∀ l l≈ → HasInitial (Setoids l l≈)
  hasInitial l l≈ = record
      { Zero = Zero
      ; isInitial = isInitial
      }
