module Cats.Category.Zero where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Level

open import Cats.Category


Zero : ∀ lo la l≈ → Category lo la l≈
Zero lo la l≈ = record
    { Obj = Lift lo ⊥
    ; _⇒_ = λ()
    ; _≈_ = λ {}
    ; id = λ{}
    ; _∘_ = λ{}
    ; equiv = λ{}
    ; ∘-resp = λ{}
    ; id-r = λ{}
    ; id-l = λ{}
    ; assoc = λ{}
    }
