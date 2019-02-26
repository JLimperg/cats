module Cats.Category.Wedges where

open import Level using (_⊔_ ; suc)
open import Relation.Binary using (Rel ; IsEquivalence)

open import Cats.Category
open import Cats.Category.Setoids using (Setoids)
open import Cats.Profunctor
open import Cats.Util.Function using (_on_ ; on-isEquivalence)


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  (F : Profunctor C C D)
  where

  private
    module C = Category C
    module D = Category D
    module F = Profunctor F


  record Wedge : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) where
    open D

    field
      Apex : Obj
      arr : ∀ x → Apex ⇒ pobj F x x
      commute : ∀ {a b} (f : a C.⇒ b)
        → pmap₂ F f ∘ arr a ≈ pmap₁ F f ∘ arr b


  Obj = Wedge


  record _⇒_ (A B : Obj) : Set (lo ⊔ la′ ⊔ l≈′) where
    open Wedge
    open D

    field
      θ : Apex A D.⇒ Apex B
      commute : ∀ x → arr B x ∘ θ ≈ arr A x


  _≈_ : ∀ {A B} → Rel (A ⇒ B) l≈′
  _≈_ = D._≈_ on _⇒_.θ


  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv = on-isEquivalence _⇒_.θ D.equiv


  id : ∀ {A} → A ⇒ A
  id = record
    { θ = D.id
    ; commute = λ x → D.id-r
    }


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  _∘_ {A} {B} {C} f g = record
    { θ = θ f ∘S θ g
    ; commute = λ j →
        begin
          arr C j ∘S θ f ∘S θ g
        ≈⟨ D.unassoc ⟩
          (arr C j ∘S θ f) ∘S θ g
        ≈⟨ D.∘-resp-l (commute f j) ⟩
          arr B j ∘S θ g
        ≈⟨ commute g j ⟩
          arr A j
        ∎
    }
    where
      open Wedge using (arr)
      open _⇒_
      open D using () renaming (_∘_ to _∘S_)
      open D.≈-Reasoning


  Wedges : Category (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) (lo ⊔ la′ ⊔ l≈′) l≈′
  Wedges = record
    { Obj = Obj
    ; _⇒_ = _⇒_
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = _∘_
    ; equiv = equiv
    ; ∘-resp = D.∘-resp
    ; id-r = D.id-r
    ; id-l = D.id-l
    ; assoc = D.assoc
    }
