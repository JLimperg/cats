{-# OPTIONS --without-K --safe #-}
module Cats.Category.Product.Binary where

open import Data.Product using (_,_) renaming (_×_ to _×T_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using
  (×-isEquivalence ; Pointwise)
open import Level using (_⊔_)
open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)


open import Cats.Category.Base


module Build {lo la l≈ lo′ la′ l≈′}
  (C : Category lo la l≈)
  (D : Category lo′ la′ l≈′)
  where

  infixr 9 _∘_
  infixr 4 _≈_


  private
    module C = Category C
    module D = Category D


  Obj : Set (lo ⊔ lo′)
  Obj = C.Obj ×T D.Obj


  _⇒_ : Obj → Obj → Set (la ⊔ la′)
  (A , A′) ⇒ (B , B′) = (A C.⇒ B) ×T (A′ D.⇒ B′)


  _≈_ : ∀ {A B} → Rel (A ⇒ B) (l≈ ⊔ l≈′)
  _≈_ = Pointwise C._≈_ D._≈_


  id : {A : Obj} → A ⇒ A
  id = C.id , D.id


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  (f , f′) ∘ (g , g′) = f C.∘ g , f′ D.∘ g′


  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv = ×-isEquivalence C.equiv D.equiv


  ∘-resp : ∀ {A B C} → _∘_ {A} {B} {C} Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ∘-resp (eq₁ , eq₁′) (eq₂ , eq₂′) = C.∘-resp eq₁ eq₂ , D.∘-resp eq₁′ eq₂′


  id-r : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
  id-r = C.id-r , D.id-r


  id-l : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
  id-l = C.id-l , D.id-l


  assoc : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
    → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
  assoc = C.assoc , D.assoc


  _×_ : Category (lo ⊔ lo′) (la ⊔ la′) (l≈ ⊔ l≈′)
  _×_ = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = ∘-resp
      ; id-r = id-r
      ; id-l = id-l
      ; assoc = assoc
      }

open Build public using (_×_)
