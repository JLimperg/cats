{-# OPTIONS --without-K --safe #-}
open import Relation.Binary.PropositionalEquality using
  ( _≡_ ; refl ; sym ; trans ; subst ; cong )

module Cats.Category.Discrete {li} {I : Set li}
  (I-set : ∀ {i j : I} (p q : i ≡ j) → p ≡ q)
  where

open import Data.Product using (Σ-syntax ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤)
open import Level

open import Cats.Category.Base
open import Cats.Functor using (Functor)


Obj : Set li
Obj = I


data _⇒_ : Obj → Obj → Set li where
  id : ∀ {A} → A ⇒ A


⇒-contr : ∀ {A B} (f : A ⇒ B)
  → Σ[ p ∈ A ≡ B ] (subst (_⇒ B) p f ≡ id)
⇒-contr id = refl , refl


⇒-contr′ : ∀ {A} (f : A ⇒ A)
  → f ≡ id
⇒-contr′ f with ⇒-contr f
... | A≡A , f≡id rewrite I-set A≡A refl = f≡id


⇒-prop : ∀ {A B} (f g : A ⇒ B) → f ≡ g
⇒-prop {A} {B} id g = sym (⇒-contr′ g)


_∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
id ∘ id = id


Discrete : Category li li zero
Discrete = record
    { Obj = Obj
    ; _⇒_ = _⇒_
    ; _≈_ = λ _ _ → ⊤
    ; id = id
    ; _∘_ = _∘_
    ; equiv = _
    ; ∘-resp = _
    ; id-r = _
    ; id-l = _
    ; assoc = _
    }


functor : ∀ {lo la l≈} {C : Category lo la l≈}
  → (I → Category.Obj C)
  → Functor Discrete C
functor {C = C} f = record
    { fobj = f
    ; fmap = fmap
    ; fmap-resp = λ {A} {B} {g} {h} _ → C.≈.reflexive (cong fmap (⇒-prop g h))
    ; fmap-id = C.≈.refl
    ; fmap-∘ = λ { {f = id} {id} → C.id-l }
    }
  where
    module C = Category C

    fmap : ∀ {A B} (g : A ⇒ B) → f A C.⇒ f B
    fmap id = C.id
