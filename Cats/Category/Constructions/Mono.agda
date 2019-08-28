{-# OPTIONS --without-K --safe #-}
module Cats.Category.Constructions.Mono where

open import Level

open import Cats.Category.Base

module Build {lo la l≈} (Cat : Category lo la l≈) where

  private open module Cat = Category Cat
  open Cat.≈-Reasoning


  IsMono : ∀ {A B} → A ⇒ B → Set (lo ⊔ la ⊔ l≈)
  IsMono {A} f = ∀ {C} {g h : C ⇒ A} → f ∘ g ≈ f ∘ h → g ≈ h


open Build public
