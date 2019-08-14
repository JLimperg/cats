module Cats.Category.Cat.Facts.Initial where

open import Cats.Category
open import Cats.Category.Cat using (Cat)
open import Cats.Category.Zero using (Zero)
open import Cats.Functor


Absurd : ∀ {lo la l≈ lo′ la′ l≈′} (C : Category lo′ la′ l≈′)
  → Functor (Zero lo la l≈) C
Absurd C = record
  { fobj = λ()
  ; fmap = λ{}
  ; fmap-resp = λ{}
  ; fmap-id = λ{}
  ; fmap-∘ = λ{}
  }


instance
  hasInitial : ∀ {lo la l≈} → HasInitial (Cat lo la l≈)
  hasInitial {lo} {la} {l≈} = record
    { ⊥ = Zero lo la l≈
    ; isInitial = λ X → record
      { arr = Absurd X
      ; unique = λ x → record
        { iso = λ{}
        ; forth-natural = λ{}
        }
      }
    }
