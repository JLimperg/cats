{-# OPTIONS --without-K --safe #-}
module Cats.Category.Setoids.Facts.Exponential where

open import Data.Product using (_,_)
open import Relation.Binary using (Setoid)

open import Cats.Category
open import Cats.Category.Setoids as Setoids using (Setoids ; ≈-intro ; ≈-elim)
open import Cats.Category.Setoids.Facts.Product as Products using
  (hasBinaryProducts)
open import Cats.Util.Conv
open import Cats.Util.SetoidReasoning

import Relation.Binary.PropositionalEquality as ≡

import Cats.Category.Base as Base

module Build l where

  infixr 1 _↝_


  open Base.Category (Setoids l l)
  open Category (Setoids l l) using (∃!-intro ; Exp ; IsUniqueSuchThat)
  open Setoids._⇒_ using (resp)
  open HasBinaryProducts (hasBinaryProducts {l} {l})


  _↝_ : Obj → Obj → Obj
  A ↝ B = record
      { Carrier = A ⇒ B
      ; _≈_ = _≈_ {A} {B}
      ; isEquivalence = equiv
      }


  eval : ∀ {B C} → (B ↝ C) × B ⇒ C
  eval = record
      { arr = λ { (f , x) → (f ⃗) x }
      ; resp = λ { (eq₁ , eq₂) → ≈-elim eq₁ eq₂ }
      }


  curry : ∀ {A B C} → A × B ⇒ C → A ⇒ B ↝ C
  curry {A} f = record
      { arr = λ a → record
           { arr = λ b → (f ⃗) (a , b)
           ; resp = λ eqb → resp f (refl , eqb)
           }
      ; resp = λ eqa → ≈-intro λ eqb → resp f (eqa , eqb)
      }
    where
      open Setoid A using (refl)


  curry-correct : ∀ {A B C} (f : A × B ⇒ C)
    → eval ∘ ⟨ curry f × id ⟩ ≈ f
  curry-correct f = ≈-intro (resp f)


  curry-unique : ∀ {A B C} (f : A × B ⇒ C)
    → IsUniqueSuchThat (λ f̃ → eval ∘ ⟨ f̃ × id ⟩ ≈ f) (curry f)
  curry-unique {A} {B} {C} f {g} eval∘g≈f
      = ≈-intro λ {a} {a′} a≈a′ → ≈-intro λ {b} {b′} b≈b′ →
        begin⟨ C ⟩
          ((((curry f) ⃗) a) ⃗) b
        ≡⟨⟩
          (f ⃗) (a , b)
        ≈˘⟨ ≈-elim eval∘g≈f (A .sym a≈a′ , B .sym b≈b′) ⟩
          (((g ⃗) a′) ⃗) b′
        ∎
    where
      open Setoid using (sym)


  _↝′_ : ∀ B C → Exp B C
  B ↝′ C = record
      { Cᴮ = B ↝ C
      ; eval = eval
      ; curry′ = λ f → ∃!-intro
          (curry f)
          (curry-correct f)
          (λ {g} eval∘g≈f → curry-unique f {g} eval∘g≈f)
      }


instance
  hasExponentials : ∀ {l} → HasExponentials (Setoids l l)
  hasExponentials {l} = record { _↝′_ = Build._↝′_ l }
