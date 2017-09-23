module Cats.Category.Zero where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Level

open import Cats.Category


Zero : Category zero zero zero
Zero = record
    { Obj = ⊥
    ; _⇒_ = λ()
    ; _≈_ = λ {}
    ; id = λ{}
    ; _∘_ = λ{}
    ; ≈-equiv = λ{}
    ; ∘-preserves-≈ = λ{}
    ; id-identity-r = λ{}
    ; id-identity-l = λ{}
    ; ∘-assoc = λ{}
    }
