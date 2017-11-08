module Cats.Functor.Representable where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Cats.Category
open import Cats.Category.Sets using (Sets)
open import Cats.Functor


module _ {lo la l≈} {C : Category lo la l≈}
  (compat : ∀ {A B} {f g : Category._⇒_ C A B} → Category._≈_ C f g → f ≡ g)
  -- TODO To eliminate compat, we'll have to generalise the category Sets,
  -- parameterising it over an equivalence relation.
  where

  private
    module C = Category C
    instance _ = C

  open Category {{...}}

  Hom : Obj → Functor C (Sets la)
  Hom X = record
      { fobj = λ A → X ⇒ A
      ; fmap = λ g f → g ∘ f
      ; fmap-resp = λ i≈j g → compat (∘-resp i≈j C.≈.refl)
      ; fmap-id = λ x → compat id-l
      ; fmap-∘ = λ f g h → compat (assoc _ _ _)
      }
