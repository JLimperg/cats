module Cats.Category.Base where

open import Level
open import Relation.Binary using
  (Rel ; IsEquivalence ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_ ; Setoid)
open import Relation.Binary.EqReasoning as EqReasoning

import Cats.Util.SetoidReasoning as SetoidR


record Category lo la l≈ : Set (suc (lo ⊔ la ⊔ l≈)) where
  infixr  9 _∘_
  infix   4 _≈_
  infixr  -1 _⇒_

  field
    Obj : Set lo
    _⇒_ : Obj → Obj → Set la
    _≈_ : ∀ {A B} → Rel (A ⇒ B) l≈
    id : {O : Obj} → O ⇒ O
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    ∘-resp : ∀ {A B C} → (_∘_ {A} {B} {C}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    id-r : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    id-l : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    assoc : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
      → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)


  Hom : (A B : Obj) → Setoid la l≈
  Hom A B = record
      { Carrier = A ⇒ B
      ; _≈_ = _≈_
      ; isEquivalence = equiv
      }


  module ≈ {A B} = IsEquivalence (equiv {A} {B})

  module ≈-Reasoning {A B} where

    open EqReasoning (Hom A B) public

    triangle = SetoidR.triangle (Hom A B)


  unassoc : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
    → f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
  unassoc = ≈.sym assoc


  ∘-resp-r : ∀ {A B C} {f : B ⇒ C} → (_∘_ {A} f) Preserves _≈_ ⟶ _≈_
  ∘-resp-r eq = ∘-resp ≈.refl eq


  ∘-resp-l :  ∀ {A B C} {g : A ⇒ B} → (λ f → _∘_ {C = C} f g) Preserves _≈_ ⟶ _≈_
  ∘-resp-l eq = ∘-resp eq ≈.refl
