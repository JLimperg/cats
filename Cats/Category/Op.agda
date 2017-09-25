module Cats.Category.Op where

open import Relation.Binary using (Rel ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡
open import Level

open import Cats.Category
open import Cats.Category.Cat using (Cat)


module _  {lo la l≈} (C : Category lo la l≈) where

  infixr 9 _∘_
  infixr 4 _≈_

  private
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

  ∘-resp : ∀ {A B C} → _∘_ {A} {B} {C} Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ∘-resp {x = f} {g} {h} {i} f≈g h≈i = C.∘-resp h≈i f≈g

  assoc : ∀ {A B C D} (f : C ⇒ D) (g : B ⇒ C) (h : A ⇒ B)
    → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
  assoc f g h = ≈.sym (C.assoc h g f)

  _ᵒᵖ : Category lo la l≈
  _ᵒᵖ = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = λ f g → g C.∘ f
      ; equiv = C.equiv
      ; ∘-resp = ∘-resp
      ; id-r = C.id-l
      ; id-l = C.id-r
      ; assoc = assoc
      }


module _ {lo la l≈ : Level} where

  private module Cat = Category (Cat lo la l≈)

  op-involution : {C : Category lo la l≈} → ((C ᵒᵖ) ᵒᵖ) Cat.≅ C
  op-involution {C} = record
      { forth = record
          { fobj = λ x → x
          ; fmap = λ f → f
          ; fmap-preserves-≈ = λ eq → eq
          ; id-preservation = C.≈.reflexive ≡.refl
          ; ∘-commut = λ _ _ → C.≈.reflexive ≡.refl
          }
      ; back = record
          { fobj = λ x → x
          ; fmap = λ f → f
          ; fmap-preserves-≈ = λ eq → eq
          ; id-preservation = C.≈.reflexive ≡.refl
          ; ∘-commut = λ _ _ → C.≈.reflexive ≡.refl
          }
      ; back-forth = record
          { iso = record
              { forth = C.id
              ; back = C.id
              ; back-forth = C.id-l
              ; forth-back = C.id-l
              }
          ; fmap-≈ = λ f → ≈.sym (≈.trans C.id-l C.id-r)
          }
      ; forth-back = record
          { iso = record
              { forth = C.id
              ; back = C.id
              ; back-forth = C.id-l
              ; forth-back = C.id-r
              }
          ; fmap-≈ = λ f → ≈.sym (≈.trans C.id-l C.id-r)
          }
      }
    where
      module C = Category C
      module ≈ = C.≈
