module Cats.Functor where

open import Cats.Category.Base
open import Level
open import Relation.Binary using (_Preserves_⟶_)

import Cats.Category.Constructions.Iso as Iso


record Functor {lo la l≈ lo′ la′ l≈′}
  (C : Category lo la l≈)
  (D : Category lo′ la′ l≈′)
  : Set (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′) where
  private
    module C = Category C
    module C≅ = Iso.Build C
    module D = Category D
    module D≅ = Iso.Build D

  field
    fobj : C.Obj → D.Obj
    fmap : ∀ {A B} → A C.⇒ B → fobj A D.⇒ fobj B
    fmap-resp : ∀ {A B} → fmap {A} {B} Preserves C._≈_ ⟶ D._≈_
    fmap-id : ∀ {A} → fmap (C.id {A}) D.≈ D.id
    fmap-∘ : ∀ {A B C} (f : B C.⇒ C) (g : A C.⇒ B)
      → fmap (f C.∘ g) D.≈ fmap f D.∘ fmap g


  fobj-preserves-≅ : fobj Preserves C≅._≅_ ⟶ D≅._≅_
  fobj-preserves-≅ {i} {j} x≅y
      = record
      { forth = fmap (forth x≅y)
      ; back = fmap (back x≅y)
      ; back-forth
          = begin
              fmap (back x≅y) D.∘ fmap (forth x≅y)
            ≈⟨ ≈.sym (fmap-∘ _ _) ⟩
              fmap (back x≅y C.∘ forth x≅y)
            ≈⟨  fmap-resp (back-forth x≅y) ⟩
              fmap C.id
            ≈⟨ fmap-id ⟩
              D.id
            ∎
      ; forth-back
          = begin
            fmap (forth x≅y) D.∘ fmap (back x≅y)
          ≈⟨ ≈.sym (fmap-∘ _ _) ⟩
            fmap (forth x≅y C.∘ back x≅y)
          ≈⟨ fmap-resp (forth-back x≅y) ⟩
            fmap C.id
          ≈⟨ fmap-id ⟩
            D.id
          ∎
      }
    where
      open C≅._≅_
      module ≈ = D.≈
      open D.≈-Reasoning
