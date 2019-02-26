module Cats.Ditrans where

open import Level using (Level ; _⊔_)

open import Cats.Category
open import Cats.Category.Setoids using (Setoids)
open import Cats.Profunctor


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  private
    module C = Category C
    open Category D


  record Ditrans (F G : Profunctor C C D) : Set (lo ⊔ la ⊔ la′ ⊔ l≈′)
    where
    field
      dicomponent : ∀ c → pobj F c c ⇒ pobj G c c
      dinatural : ∀ {a b} (f : a C.⇒ b)
        → pmap₂ G f ∘ dicomponent a ∘ pmap₁ F f
        ≈ pmap₁ G f ∘ dicomponent b ∘ pmap₂ F f
