module Cats.Category.Setoids where

open import Cats.Util.SetoidMorphism public using
  (_⇒_ ; _≈_ ; ≈-intro ; ≈-elim ; ≈-elim′ ; equiv ; _∘_ ; id ; ∘-resp ; assoc ; id-l
  ; id-r)

open import Level using (_⊔_ ; suc)
open import Relation.Binary using (Setoid)

open import Cats.Category.Base
open import Cats.Category.Sets using (Sets)
open import Cats.Util.Conv


instance
  HasArrow-⇒ : ∀ {l l≈} {A B : Setoid l l≈}
    → HasArrow (A ⇒ B) (suc l) l l
  HasArrow-⇒ {l} = record { Cat = Sets l ; _⃗ = _⇒_.arr }


Setoids : ∀ l l≈ → Category (suc (l ⊔ l≈)) (l ⊔ l≈) (l ⊔ l≈)
Setoids l l≈ = record
    { Obj = Setoid l l≈
    ; _⇒_ = λ A B → A ⇒ B
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = _∘_
    ; equiv = equiv
    ; ∘-resp = λ {A} {B} {C} {f} {g} {h} {i} → ∘-resp {f = f} {g} {h} {i}
    ; id-r = λ {A} {B} {f} → id-r {f = f}
    ; id-l = λ {A} {B} {f} → id-l {f = f}
    ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → assoc {f = f} {g} {h}
    }
