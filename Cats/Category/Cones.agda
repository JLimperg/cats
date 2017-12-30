module Cats.Category.Cones where

open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Level using (_⊔_)

open import Cats.Category
open import Cats.Functor
open import Cats.Util.Conv

import Cats.Util.Function as Fun


module _ {lo la l≈ lo′ la′ l≈′}
  {J : Category lo la l≈}
  {Z : Category lo′ la′ l≈′}
  (D : Functor J Z)
  where

  infixr 9 _∘_
  infixr 4 _≈_

  private
    module Z = Category Z
    module J = Category J
    module D = Functor D


  record Cone : Set (lo ⊔ la ⊔ la′ ⊔ lo′ ⊔ l≈′) where
    field
      Apex : Z.Obj
      arr : ∀ j → Apex Z.⇒ D.fobj j
      commute : ∀ {i j} (α : i J.⇒ j) → arr j Z.≈ D.fmap α Z.∘ arr i


  instance
    HasObj-Cone : HasObj Cone lo′ la′ l≈′
    HasObj-Cone = record { Cat = Z ; _ᴼ = Cone.Apex }


  Obj = Cone


  record _⇒_ (A B : Obj) : Set (lo ⊔ la′ ⊔ l≈′) where
    private
      module A = Cone A ; module B = Cone B

    field
      θ : A.Apex Z.⇒ B.Apex
      commute : ∀ j → B.arr j Z.∘ θ Z.≈ A.arr j


  instance
    HasArrow-⇒ : ∀ {A B} → HasArrow (A ⇒ B) lo′ la′ l≈′
    HasArrow-⇒ = record { Cat = Z ; _⃗ = _⇒_.θ }


  _≈_ : ∀ {A B} → Rel (A ⇒ B) l≈′
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
      { θ = f ⃗ Z.∘ g ⃗
      ; commute = λ j →
          begin
            arr C j Z.∘ f ⃗ Z.∘ g ⃗
          ≈⟨ Z.unassoc ⟩
            (arr C j Z.∘ f ⃗) Z.∘ g ⃗
          ≈⟨ Z.∘-resp-l (commute f j) ⟩
            arr B j Z.∘ g ⃗
          ≈⟨ commute g j ⟩
            arr A j
          ∎
      }
    where
      open Cone using (arr)
      open _⇒_ using (commute)
      open Z.≈-Reasoning


  Cones : Category (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) (lo ⊔ la′ ⊔ l≈′) l≈′
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
      ; assoc = Z.assoc
      }


  open Category Cones using (_≅_)


  cone-iso→obj-iso : ∀ {c d : Cone}
    → c ≅ d
    → c ᴼ Z.≅ d ᴼ
  cone-iso→obj-iso i = record
      { forth = forth i ⃗
      ; back = back i ⃗
      ; back-forth = back-forth i
      ; forth-back = forth-back i
      }
    where
      open _≅_
