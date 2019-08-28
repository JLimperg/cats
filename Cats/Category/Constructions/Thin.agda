{-# OPTIONS --without-K --safe #-}
module Cats.Category.Constructions.Thin where

open import Cats.Category.Base

open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)


module _ {lo la l≈} (C : Category lo la l≈) where

  open Category C


  Thin : Set (lo ⊔ la ⊔ l≈)
  Thin = ∀ {A B} {f g : A ⇒ B} → f ≈ g


  StronglyThin : Set (lo ⊔ la)
  StronglyThin = ∀ {A B} {f g : A ⇒ B} → f ≡ g


StronglyThin→Thin : ∀ {lo la l≈} {C : Category lo la l≈}
  → StronglyThin C → Thin C
StronglyThin→Thin {C = C} sthin = ≈.reflexive sthin
  where
    open Category C
