module Cats.Functor.Representable where

open import Relation.Binary using (Setoid)

open import Cats.Category
open import Cats.Category.Setoids using (Setoids)
open import Cats.Functor


module _ {lo la l≈} {C : Category lo la l≈} where

  open module C = Category C renaming (Hom to Homset)


  Hom : Obj → Functor C (Setoids la l≈)
  Hom X = record
      { fobj = λ A → Homset X A
      ; fmap = λ f → record
          { arr = λ g → f ∘ g
          ; resp = ∘-resp C.≈.refl
          }
      ; fmap-resp = λ _ → ∘-resp C.≈.refl
      ; fmap-id = ∘-resp C.≈.refl
      ; fmap-∘ = λ _ _ → ∘-resp C.≈.refl
      }
