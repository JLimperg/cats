module Cats.Functor where

open import Level
open import Relation.Binary using (_Preserves_⟶_)

open import Cats.Category.Base
open import Cats.Util.Function using () renaming (_∘_ to _⊙_)

import Cats.Category.Constructions.Iso as Iso


infixr 9 _∘_


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


  fobj-resp : fobj Preserves C≅._≅_ ⟶ D≅._≅_
  fobj-resp {i} {j} x≅y
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


id : ∀ {lo la l≈} {C : Category lo la l≈} → Functor C C
id {C = C} = record
    { fobj = λ x → x
    ; fmap = λ f → f
    ; fmap-resp = λ eq → eq
    ; fmap-id = C.≈.refl
    ; fmap-∘ = λ _ _ → C.≈.refl
    }
  where
    module C = Category C


_∘_ : ∀ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  → {C : Category lo la l≈}
  → {D : Category lo′ la′ l≈′}
  → {E : Category lo″ la″ l≈″}
  → Functor D E → Functor C D → Functor C E
_∘_ {C = C} {D} {E} F G = record
    { fobj = F.fobj ⊙ G.fobj
    ; fmap = F.fmap ⊙ G.fmap
    ; fmap-resp = F.fmap-resp ⊙ G.fmap-resp
    ; fmap-id = ≈.trans (F.fmap-resp G.fmap-id) F.fmap-id
    ; fmap-∘ = λ f g → ≈.trans (F.fmap-resp (G.fmap-∘ _ _)) (F.fmap-∘ _ _)
    }
  where
    module F = Functor F
    module G = Functor G
    module E = Category E
    module ≈ = E.≈
