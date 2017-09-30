module Cats.Category.One where

open import Data.Unit using (⊤ ; tt)
open import Level

open import Cats.Category


One : ∀ lo la l≈ → Category lo la l≈
One lo la l≈ = record
    { Obj = Lift ⊤
    ; _⇒_ = λ _ _ → Lift ⊤
    ; _≈_ = λ _ _ → Lift ⊤
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
    ; assoc = λ _ _ _ → lift tt
    }
