module Cats.Category.Cones where

open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Level using (_⊔_)

open import Cats.Category
open import Cats.Functor

import Cats.Util.Function as Fun


module _ {lo la l≈} {J Z : Category lo la l≈} (D : Functor J Z) where

  infixr 9 _∘_
  infixr 4 _≈_

  private
    module Z = Category Z
    module J = Category J
    module D = Functor D


  record Cone : Set (lo ⊔ la ⊔ l≈) where
    field
      Apex : Z.Obj
      arr : ∀ j → Apex Z.⇒ D.fobj j
      commute : ∀ {i j} (α : i J.⇒ j) → arr j Z.≈ D.fmap α Z.∘ arr i


  Obj = Cone


  record _⇒_ (A B : Obj) : Set (lo ⊔ la ⊔ l≈) where
    private
      module A = Cone A ; module B = Cone B

    field
      θ : A.Apex Z.⇒ B.Apex
      commute : ∀ j → B.arr j Z.∘ θ Z.≈ A.arr j


  _≈_ : ∀ {A B} → Rel (A ⇒ B) l≈
  _≈_ = Z._≈_ Fun.on _⇒_.θ


  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv = Fun.on-isEquivalence _⇒_.θ Z.equiv


  id : ∀ {A} → A ⇒ A
  id = record
      { θ = Z.id
      ; commute = λ j → Z.id-r
      }


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  _∘_ {A} {B} {C} f g = record
      { θ = θ f Z.∘ θ g
      ; commute = λ j →
          begin
            arr C j Z.∘ θ f Z.∘ θ g
          ≈⟨ sym (Z.assoc _ _ _) ⟩
            (arr C j Z.∘ θ f) Z.∘ θ g
          ≈⟨ Z.∘-resp (commute f j) refl ⟩
            arr B j Z.∘ θ g
          ≈⟨ commute g j ⟩
            arr A j
          ∎
      }
    where
      open Cone ; open _⇒_ ; open Z.≈ ; open Z.≈-Reasoning


  Cones : Category (lo ⊔ la ⊔ l≈) (lo ⊔ la ⊔ l≈) l≈
  Cones = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = Z.∘-resp
      ; id-r = Z.id-r
      ; id-l = Z.id-l
      ; assoc = λ _ _ _ → Z.assoc _ _ _
      }
