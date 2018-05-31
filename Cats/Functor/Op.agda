module Cats.Functor.Op where

open import Cats.Category.Base
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Functor using (Functor)

open Functor


Op : ∀ {lo la l≈ lo′ la′ l≈′}
  → {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  → Functor C D
  → Functor (C ᵒᵖ) (D ᵒᵖ)
Op F = record
    { fobj = fobj F
    ; fmap = fmap F
    ; fmap-resp = fmap-resp F
    ; fmap-id = fmap-id F
    ; fmap-∘ = λ f g → fmap-∘ F g f
    }
