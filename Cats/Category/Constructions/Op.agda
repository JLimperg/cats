open import Cats.Category

module Cats.Category.Constructions.Op {lo la l≈} (C : Category lo la l≈) where

open import Relation.Binary using (Rel ; _Preserves₂_⟶_⟶_)

infixr 9 _∘_
infixr 4 _≈_

module C = Category C
module ≈ = C.≈

Obj : Set lo
Obj = C.Obj

_⇒_ : Obj → Obj → Set la
A ⇒ B = B C.⇒ A

id : ∀ {A} → A ⇒ A
id = C.id

_∘_ : ∀ {A B C : Obj} → (B ⇒ C) → (A ⇒ B) → A ⇒ C
f ∘ g = g C.∘ f

_≈_ : ∀ {A B} → Rel (A ⇒ B) l≈
_≈_ = C._≈_

∘-preserves-≈ : ∀ {A B C} → _∘_ {A} {B} {C} Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
∘-preserves-≈ {x = f} {g} {h} {i} f≈g h≈i = C.∘-preserves-≈ h≈i f≈g

∘-assoc : ∀ {A B C D} (f : C ⇒ D) (g : B ⇒ C) (h : A ⇒ B)
  → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
∘-assoc f g h = ≈.sym (C.∘-assoc h g f)

_ᵒᵖ : Category lo la l≈
_ᵒᵖ = record
    { Obj = Obj
    ; _⇒_ = _⇒_
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = λ f g → g C.∘ f
    ; ≈-equiv = C.≈-equiv
    ; ∘-preserves-≈ = ∘-preserves-≈
    ; id-identity-r = C.id-identity-l
    ; id-identity-l = C.id-identity-r
    ; ∘-assoc = ∘-assoc
    }
