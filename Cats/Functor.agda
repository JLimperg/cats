module Cats.Functor where

open import Cats.Category
open import Level
open import Relation.Binary using (_Preserves_⟶_)


record Functor {lo la l≈}
  (C : Category lo la l≈)
  (D : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈) where
  private
    module C = Category C
    module D = Category D

  field
    fobj : C.Obj → D.Obj
    fmap : ∀ {A B} → A C.⇒ B → fobj A D.⇒ fobj B
    fmap-preserves-≈ : ∀ {A B} → fmap {A} {B} Preserves C._≈_ ⟶ D._≈_
    id-preservation : ∀ {A} → fmap (C.id {A}) D.≈ D.id
    ∘-commut : ∀ {a b c} (f : b C.⇒ c) (g : a C.⇒ b)
      → fmap (f C.∘ g) D.≈ fmap f D.∘ fmap g


  fobj-preserves-≅ : fobj Preserves C._≅_ ⟶ D._≅_
  fobj-preserves-≅ {i} {j} x≅y
      = record
      { forth = fmap (forth x≅y)
      ; back = fmap (back x≅y)
      ; back-forth
          = begin
              fmap (back x≅y) D.∘ fmap (forth x≅y)
            ≈⟨ ≈.sym (∘-commut _ _) ⟩
              fmap (back x≅y C.∘ forth x≅y)
            ≈⟨  fmap-preserves-≈ (back-forth x≅y) ⟩
              fmap C.id
            ≈⟨ id-preservation ⟩
              D.id
            ∎
      ; forth-back
          = begin
            fmap (forth x≅y) D.∘ fmap (back x≅y)
          ≈⟨ ≈.sym (∘-commut _ _) ⟩
            fmap (forth x≅y C.∘ back x≅y)
          ≈⟨  fmap-preserves-≈ (forth-back x≅y) ⟩
            fmap C.id
          ≈⟨ id-preservation ⟩
            D.id
          ∎
      }
    where
      open C._≅_
      module ≈ = D.≈
      open D.≈-Reasoning
