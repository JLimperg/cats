module Cats.Category.Setoids where

open import Level using (Level ; _⊔_ ; suc)
open import Relation.Binary using
  (Setoid ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_ ; Rel ; IsEquivalence)

open import Cats.Category.Base
open import Cats.Category.Sets using (Sets)
open import Cats.Util.Conv
open import Cats.Util.Function using () renaming (_∘_ to _⊚_)


open Setoid renaming (_≈_ to eq)


module Build (l l≈ : Level) where

  infixr 9 _∘_
  infixr 4 _≈_


  Obj : Set (suc (l ⊔ l≈))
  Obj = Setoid l l≈


  record _⇒_ (A B : Obj) : Set (l ⊔ l≈) where
    field
      arr : Carrier A → Carrier B
      resp : arr Preserves eq A ⟶ eq B

  open _⇒_ using (resp)


  instance
    HasArrow-⇒ : ∀ A B → HasArrow (A ⇒ B) (suc l) l l
    HasArrow-⇒ A B = record { Cat = Sets l ; _⃗ = _⇒_.arr }


  _≈_ : ∀ {A B} → Rel (A ⇒ B) (l ⊔ l≈)
  _≈_ {A} {B} f g = ∀ {x y} → eq A x y → eq B ((f ⃗) x) ((g ⃗) y)


  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv {A} {B} = record
      { refl = λ {f} → resp f
      ; sym = λ eq x≈y → B.sym (eq (A.sym x≈y))
      ; trans = λ eq₁ eq₂ x≈y → B.trans (eq₁ x≈y) (eq₂ A.refl)
      }
    where
      module A = Setoid A
      module B = Setoid B


  id : ∀ {A} → A ⇒ A
  id {X} = record { arr = λ x → x ; resp = λ x → x }


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  _∘_ {C = C} f g = record
      { arr = f ⃗ ⊚ g ⃗
      ; resp = resp f ⊚ resp g
      }


  assoc : ∀ {A B C D} (f : C ⇒ D) (g : B ⇒ C) (h : A ⇒ B)
    → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
  assoc f g h eqA = resp f (resp g (resp h eqA))


  Setoids : Category (suc (l ⊔ l≈)) (l ⊔ l≈) (l ⊔ l≈)
  Setoids = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = λ f≈g h≈i x≈y → f≈g (h≈i x≈y)
      ; id-r = λ {A} {B} {f} → resp f
      ; id-l = λ {A} {B} {f} → resp f
      ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → assoc f g h
      }


open Build public using (Setoids)
