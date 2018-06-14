module Cats.Category.Discrete {li} (I : Set li) where

open import Data.Unit using (⊤)
open import Level

open import Cats.Category.Base
open import Cats.Functor using (Functor)


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


functor : ∀ {lo la l≈} {C : Category lo la l≈}
  → (I → Category.Obj C)
  → Functor Discrete C
functor {C = C} f = record
    { fobj = f
    ; fmap = λ { id → C.id }
    ; fmap-resp = λ { {_} {_} {id} {id} _ → C.≈.refl }
    ; fmap-id = C.≈.refl
    ; fmap-∘ = λ { {f = id} {id} → C.id-l }
    }
  where
    module C = Category C
