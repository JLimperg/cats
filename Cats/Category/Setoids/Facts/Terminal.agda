module Cats.Category.Setoids.Facts.Terminal where

open import Data.Unit using (⊤)
open import Level

open import Cats.Category
open import Cats.Category.Setoids using (Setoids)


module Build {l} {l≈} where

  open Category (Setoids l l≈)


  One : Obj
  One = record
      { Carrier = Lift l ⊤
      ; _≈_ = λ _ _ → Lift l≈ ⊤
      }


  isTerminal : IsTerminal One
  isTerminal X = ∃!-intro _ _ _


open Build


instance
  hasTerminal : ∀ {l l≈} → HasTerminal (Setoids l l≈)
  hasTerminal = record
      { One = One
      ; isTerminal = isTerminal
      }
