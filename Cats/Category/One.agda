{-# OPTIONS --without-K --safe #-}
module Cats.Category.One where

open import Data.Unit using (⊤ ; tt)
open import Level

open import Cats.Category.Base


One : ∀ lo la l≈ → Category lo la l≈
One lo la l≈ = record
    { Obj = Lift lo ⊤
    ; _⇒_ = λ _ _ → Lift la ⊤
    ; _≈_ = λ _ _ → Lift l≈ ⊤
    ; id = lift tt
    ; _∘_ = λ _ _ → lift tt
    ; equiv
        = record
        { refl = lift tt
        ; sym = λ _ → lift tt
        ; trans = λ _ _ → lift tt
        }
    ; ∘-resp = λ _ _ → lift tt
    ; id-r = lift tt
    ; id-l = lift tt
    ; assoc = lift tt
    }
