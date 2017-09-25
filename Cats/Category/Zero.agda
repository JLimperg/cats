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
    ; equiv = λ{}
    ; ∘-resp = λ{}
    ; id-r = λ{}
    ; id-l = λ{}
    ; assoc = λ{}
    }
