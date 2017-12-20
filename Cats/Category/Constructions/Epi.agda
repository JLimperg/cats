module Cats.Category.Constructions.Epi where

open import Level

open import Cats.Category.Base

module Build {lo la l≈} (Cat : Category lo la l≈) where

  private open module Cat = Category Cat
  open Cat.≈-Reasoning


  IsEpi : ∀ {A B} → A ⇒ B → Set (lo ⊔ la ⊔ l≈)
  IsEpi {A} {B} f = ∀ {C} {g h : B ⇒ C} → g ∘ f ≈ h ∘ f → g ≈ h
