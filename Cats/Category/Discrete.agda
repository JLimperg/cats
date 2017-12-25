module Cats.Category.Discrete {li} (I : Set li) where

open import Data.Unit using (⊤)
open import Level

open import Cats.Category


Obj : Set li
Obj = I


data _⇒_ : Obj → Obj → Set where
  id : ∀ {A} → A ⇒ A


_∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
id ∘ id = id


Discrete : Category li zero zero
Discrete = record
    { Obj = Obj
    ; _⇒_ = _⇒_
    ; _≈_ = λ _ _ → ⊤
    ; id = id
    ; _∘_ = _∘_
    ; equiv = _
    ; ∘-resp = _
    ; id-r = _
    ; id-l = _
    ; assoc = _
    }
