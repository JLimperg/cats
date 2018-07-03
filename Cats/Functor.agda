module Cats.Functor where

open import Level
open import Relation.Binary using (_Preserves_⟶_)

open import Cats.Category.Base
open import Cats.Util.Function using () renaming (_∘_ to _⊙_)
open import Cats.Util.SetoidMorphism using (_⇒_ ; IsInjective ; IsSurjective)
open import Cats.Util.SetoidMorphism.Iso using
  ( IsIso ; _≅_ ; IsIso→≅ ; Injective∧Surjective→Iso ; Iso→Injective
  ; Iso→Surjective )

import Cats.Category.Constructions.Iso as Iso

open Iso.Build._≅_


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
    fmap-∘ : ∀ {A B C} {f : B C.⇒ C} {g : A C.⇒ B}
      → fmap f D.∘ fmap g D.≈ fmap (f C.∘ g)


  sfmap : ∀ {a b} → C.Hom a b ⇒ D.Hom (fobj a) (fobj b)
  sfmap = record
      { arr = fmap
      ; resp = fmap-resp
      }


  fobj-resp : fobj Preserves C≅._≅_ ⟶ D≅._≅_
  fobj-resp {i} {j} x≅y
      = record
      { forth = fmap (forth x≅y)
      ; back = fmap (back x≅y)
      ; back-forth
          = begin
              fmap (back x≅y) D.∘ fmap (forth x≅y)
            ≈⟨ fmap-∘ ⟩
              fmap (back x≅y C.∘ forth x≅y)
            ≈⟨  fmap-resp (back-forth x≅y) ⟩
              fmap C.id
            ≈⟨ fmap-id ⟩
              D.id
            ∎
      ; forth-back
          = begin
            fmap (forth x≅y) D.∘ fmap (back x≅y)
          ≈⟨ fmap-∘ ⟩
            fmap (forth x≅y C.∘ back x≅y)
          ≈⟨ fmap-resp (forth-back x≅y) ⟩
            fmap C.id
          ≈⟨ fmap-id ⟩
            D.id
          ∎
      }
    where
      open D.≈-Reasoning

open Functor public


id : ∀ {lo la l≈} {C : Category lo la l≈} → Functor C C
id {C = C} = record
    { fobj = λ x → x
    ; fmap = λ f → f
    ; fmap-resp = λ eq → eq
    ; fmap-id = C.≈.refl
    ; fmap-∘ = C.≈.refl
    }
  where
    module C = Category C


_∘_ : ∀ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  → {C : Category lo la l≈}
  → {D : Category lo′ la′ l≈′}
  → {E : Category lo″ la″ l≈″}
  → Functor D E → Functor C D → Functor C E
_∘_ {E = E} F G = record
    { fobj = fobj F ⊙ fobj G
    ; fmap = fmap F ⊙ fmap G
    ; fmap-resp = fmap-resp F ⊙ fmap-resp G
    ; fmap-id = E.≈.trans (fmap-resp F (fmap-id G)) (fmap-id F)
    ; fmap-∘ = E.≈.trans (fmap-∘ F) (fmap-resp F (fmap-∘ G))
    }
  where
    module E = Category E


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D


  IsFaithful : Set (lo ⊔ la ⊔ l≈ ⊔ l≈′)
  IsFaithful = ∀ {a b} → IsInjective (sfmap F {a} {b})


  IsFull : Set (lo ⊔ la ⊔ la′ ⊔ l≈′)
  IsFull = ∀ {a b} → IsSurjective (sfmap F {a} {b})


  IsEmbedding : Set (lo ⊔ la ⊔ l≈ ⊔ la′ ⊔ l≈′)
  IsEmbedding = ∀ {a b} → IsIso (sfmap F {a} {b})


  Embedding→≅ : IsEmbedding → ∀ {a b} → C.Hom a b ≅ D.Hom (fobj F a) (fobj F b)
  Embedding→≅ embedding = IsIso→≅ (sfmap F) embedding


  Full∧Faithful→Embedding : IsFull → IsFaithful → IsEmbedding
  Full∧Faithful→Embedding full faithful
      = Injective∧Surjective→Iso faithful full


  Embedding→Full : IsEmbedding → IsFull
  Embedding→Full embedding = Iso→Surjective embedding


  Embedding→Faithful : IsEmbedding → IsFaithful
  Embedding→Faithful embedding = Iso→Injective embedding
