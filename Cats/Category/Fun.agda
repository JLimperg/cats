module Cats.Category.Fun where

open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Level

open import Cats.Category
open import Cats.Functor


record Trans {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈}
  {D : Category lo′ la′ l≈′}
  (F G : Functor C D)
  : Set (lo ⊔ la ⊔ la′ ⊔ l≈′)
  where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  field
    component : (C : C.Obj) → F.fobj C D.⇒ G.fobj C
    natural : ∀ {A B} {f : A C.⇒ B}
      → component B D.∘ F.fmap f D.≈ G.fmap f D.∘ component A

open Trans


module _ {lo la l≈ lo′ la′ l≈′}
  (C : Category lo la l≈)
  (D : Category lo′ la′ l≈′)
  where

  infixr 9 _∘_
  infixr 4 _≈_


  private
    module C = Category C
    module D = Category D

  open D.≈
  open D.≈-Reasoning


  Obj : Set (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′)
  Obj = Functor C D


  _⇒_ : Obj → Obj → Set (lo ⊔ la ⊔ la′ ⊔ l≈′)
  _⇒_ = Trans


  _∘_ : ∀ {F G H} → G ⇒ H → F ⇒ G → F ⇒ H
  _∘_ {F} {G} {H} θ ι = record
      { component = λ C → component θ C D.∘ component ι C
      ; natural = λ {A} {B} {f} →
          begin
            (component θ B D.∘ component ι B) D.∘ F.fmap f
          ≈⟨ D.assoc ⟩
            component θ B D.∘ (component ι B D.∘ F.fmap f)
          ≈⟨ D.∘-resp-r (natural ι) ⟩
            component θ B D.∘ (G.fmap f D.∘ component ι A)
          ≈⟨ D.unassoc ⟩
            (component θ B D.∘ G.fmap f) D.∘ component ι A
          ≈⟨ D.∘-resp-l (natural θ) ⟩
            (H.fmap f D.∘ component θ A) D.∘ component ι A
          ≈⟨ D.assoc ⟩
            H.fmap f D.∘ component θ A D.∘ component ι A
          ∎
      }
    where
      module F = Functor F
      module G = Functor G
      module H = Functor H


  id : ∀ {F} → F ⇒ F
  id = record
      { component = λ _ → D.id
      ; natural = trans D.id-l (sym D.id-r)
      }


  _≈_ : ∀ {F G} → Rel (F ⇒ G) (lo ⊔ l≈′)
  θ ≈ ι = ∀ C → component θ C D.≈ component ι C


  equiv : ∀ {F G} → IsEquivalence (_≈_ {F} {G})
  equiv = record
      { refl = λ _ → refl
      ; sym = λ eq C → sym (eq C)
      ; trans = λ eq₁ eq₂ C → trans (eq₁ C) (eq₂ C)
      }


  Fun : Category (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′) (lo ⊔ la ⊔ la′ ⊔ l≈′) (lo ⊔ l≈′)
  Fun = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = λ θ≈θ′ ι≈ι′ C → D.∘-resp (θ≈θ′ C) (ι≈ι′ C)
      ; id-r = λ _ → D.id-r
      ; id-l = λ _ → D.id-l
      ; assoc = λ _ → D.assoc
      }
