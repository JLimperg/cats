module Cats.Category.Setoids where

open import Level using (Level ; _⊔_ ; suc)
open import Relation.Binary using
  (Setoid ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_ ; Rel ; IsEquivalence)

open import Cats.Category


module _ (l l≈ : Level) where

  infixr 9 _∘_
  infixr 4 _≈_

  open Setoid renaming (_≈_ to eq)

  Obj : Set (suc (l ⊔ l≈))
  Obj = Setoid l l≈


  record _⇒_ (A B : Obj) : Set (l ⊔ l≈) where
    field
      arr : Carrier A → Carrier B
      resp : arr Preserves eq A ⟶ eq B

  open _⇒_


  _≈_ : ∀ {A B} → Rel (A ⇒ B) (l ⊔ l≈)
  _≈_ {A} {B} f g = ∀ {x y} → eq A x y → eq B (arr f x) (arr g y)


  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv {A} {B} = record
      { refl = λ {f} → resp f
      ; sym = λ {f} {g} eq x≈y → B.sym (eq (A.sym x≈y))
      ; trans = λ {f} eq₁ eq₂ x≈y → B.trans (eq₁ x≈y) (eq₂ A.refl)
      }
    where
      module A = Setoid A
      module B = Setoid B


  id : ∀ {A} → A ⇒ A
  id {X} = record { arr = λ x → x ; resp = λ x → x }


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  _∘_ {C = C} f g = record
      { arr = λ x → arr f (arr g x)
      ; resp = λ eq → resp f (resp g eq)
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
      ; assoc = assoc
      }

  -- [1] Splitting these definitions off into lemmas confuses type inference. I
  -- don't know why.
