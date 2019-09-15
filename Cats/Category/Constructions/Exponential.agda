{-# OPTIONS --without-K --safe #-}
module Cats.Category.Constructions.Exponential where

open import Level

open import Cats.Category.Base
open import Cats.Category.Constructions.Product as Product using
  (HasBinaryProducts)
open import Cats.Util.Conv

import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Constructions.Unique as Unique


module Build {lo la l≈}
  (Cat : Category lo la l≈)
  {{hasBinaryProducts : HasBinaryProducts Cat}}
  where

  open Category Cat
  open ≈-Reasoning
  open Unique.Build Cat
  open Iso.Build Cat
  open HasBinaryProducts hasBinaryProducts
  open _≅_


  record Exp (B C : Obj) : Set (lo ⊔ la ⊔ l≈) where
    field
      Cᴮ : Obj
      eval : Cᴮ × B ⇒ C
      curry′ : ∀ {A} (f : A × B ⇒ C)
        → ∃![ f̃ ∈ A ⇒ Cᴮ ] (eval ∘ ⟨ f̃ × id ⟩ ≈ f)


    curry : ∀ {A} → A × B ⇒ C → A ⇒ Cᴮ
    curry f = curry′ f ⃗


    eval-curry : ∀ {A} {f : A × B ⇒ C}
      → eval ∘ ⟨ curry f × id ⟩ ≈ f
    eval-curry {f = f} = ∃!′.prop (curry′ f)


    curry-unique : ∀ {A} {f : A × B ⇒ C} {g}
      → eval ∘ ⟨ g × id ⟩ ≈ f
      → curry f ≈ g
    curry-unique {f = f} = ∃!′.unique (curry′ f)


    uncurry : ∀ {A} → A ⇒ Cᴮ → A × B ⇒ C
    uncurry f = eval ∘ ⟨ f × id ⟩


    curry∘uncurry : ∀ {A} {f : A ⇒ Cᴮ}
      → curry (uncurry f) ≈ f
    curry∘uncurry = curry-unique ≈.refl


    uncurry∘curry : ∀ {A} {f : A × B ⇒ C}
      → uncurry (curry f) ≈ f
    uncurry∘curry = eval-curry


  instance HasObj-Exp : ∀ {B C} → HasObj (Exp B C) lo la l≈
  HasObj-Exp = record { Cat = Cat ; _ᴼ = Exp.Cᴮ }

  open Exp public


  curry∘curry : ∀ {A B C Y Z} (Cᴮ : Exp B C) (Yᶻ : Exp Y Z)
    → {f : Cᴮ ᴼ × Y ⇒ Z} {g : A × B ⇒ C}
    → curry Yᶻ f ∘ curry Cᴮ g ≈ curry Yᶻ (f ∘ ⟨ curry Cᴮ g × id ⟩)
  curry∘curry Cᴮ Yᶻ {f} {g} = ≈.sym (curry-unique Yᶻ (
      begin
        eval Yᶻ ∘ ⟨ curry Yᶻ f ∘ curry Cᴮ g × id ⟩
      ≈⟨ ∘-resp-r (⟨×⟩-resp ≈.refl (≈.sym id-l)) ⟩
        eval Yᶻ ∘ ⟨ curry Yᶻ f ∘ curry Cᴮ g × id ∘ id ⟩
      ≈⟨ ∘-resp-r (≈.sym ⟨×⟩-∘) ⟩
        eval Yᶻ ∘ ⟨ curry Yᶻ f × id ⟩ ∘ ⟨ curry Cᴮ g × id ⟩
      ≈⟨ unassoc ⟩
        (eval Yᶻ ∘ ⟨ curry Yᶻ f × id ⟩) ∘ ⟨ curry Cᴮ g × id ⟩
      ≈⟨ ∘-resp-l (eval-curry Yᶻ) ⟩
        f ∘ ⟨ curry Cᴮ g × id ⟩
      ∎
    ))


  Exp-resp-≅ : ∀ {A A′ B B′}
    → A ≅ A′
    → B ≅ B′
    → (E : Exp A B) (E′ : Exp A′ B′)
    → E ᴼ ≅ E′ ᴼ
  Exp-resp-≅ A≅A′ B≅B′ E E′ = record
    { forth = curry E′ (B≅B′ .forth ∘ eval E ∘ ⟨ id × A≅A′ .back ⟩)
    ; back = curry E (B≅B′ .back ∘ eval E′ ∘ ⟨ id × A≅A′ .forth ⟩)
    -- Today in our series on 'trivial' properties (also copy-and-paste
    -- programming).
    ; back-forth = ≈.trans (curry∘curry E′ E)
        (curry-unique E (≈.trans (∘-resp-r ⟨×⟩-id) (≈.trans id-r
        (≈.sym (≈.trans assoc (≈.trans (∘-resp-r (≈.trans assoc (≈.trans
        (∘-resp-r (≈.trans ⟨×⟩-∘
        (≈.trans (⟨×⟩-resp (≈.trans id-l (≈.sym id-r)) (≈.trans id-r (≈.sym id-l)))
        (≈.sym ⟨×⟩-∘)))) (≈.trans unassoc (∘-resp-l (eval-curry E′))))))
        (≈.trans unassoc (≈.trans (∘-resp-l (≈.trans unassoc
        (≈.trans (∘-resp-l (B≅B′ .back-forth)) id-l)))
        (≈.trans assoc (≈.trans (∘-resp-r (≈.trans ⟨×⟩-∘
        (≈.trans (⟨×⟩-resp id-l (A≅A′ .back-forth)) ⟨×⟩-id))) id-r))))))))))
    ; forth-back = ≈.trans (curry∘curry E E′)
        (curry-unique E′ (≈.trans (∘-resp-r ⟨×⟩-id) (≈.trans id-r
        (≈.sym (≈.trans assoc (≈.trans (∘-resp-r (≈.trans assoc (≈.trans
        (∘-resp-r (≈.trans ⟨×⟩-∘
        (≈.trans (⟨×⟩-resp (≈.trans id-l (≈.sym id-r)) (≈.trans id-r (≈.sym id-l)))
        (≈.sym ⟨×⟩-∘)))) (≈.trans unassoc (∘-resp-l (eval-curry E))))))
        (≈.trans unassoc (≈.trans (∘-resp-l (≈.trans unassoc
        (≈.trans (∘-resp-l (B≅B′ .forth-back)) id-l)))
        (≈.trans assoc (≈.trans (∘-resp-r (≈.trans ⟨×⟩-∘
        (≈.trans (⟨×⟩-resp id-l (A≅A′ .forth-back)) ⟨×⟩-id))) id-r))))))))))
    }


record HasExponentials {lo la l≈}
  (Cat : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈)
  where
  private open module Bld = Build Cat using (Exp)
  open Category Cat
  open Unique.Build Cat
  open Iso.Build Cat

  infixr 1 _↝′_ _↝_

  field
    {{hasBinaryProducts}} : HasBinaryProducts Cat
    _↝′_ : ∀ B C → Exp B C


  open HasBinaryProducts hasBinaryProducts


  _↝_ : Obj → Obj → Obj
  B ↝ C = (B ↝′ C) ᴼ


  eval : ∀ {B C} → (B ↝ C) × B ⇒ C
  eval {B} {C} = Bld.eval (B ↝′ C)


  curry : ∀ {A B C} → A × B ⇒ C → A ⇒ B ↝ C
  curry {B = B} {C} f = Bld.curry (B ↝′ C) f


  uncurry : ∀ {A B C} → A ⇒ B ↝ C → A × B ⇒ C
  uncurry {B = B} {C} = Bld.uncurry (B ↝′ C)


  eval-curry : ∀ {A B C} {f : A × B ⇒ C}
    → eval ∘ ⟨ curry f × id ⟩ ≈ f
  eval-curry {B = B} {C} = Bld.eval-curry (B ↝′ C)


  curry-unique : ∀ {A B C} {f : A × B ⇒ C} {g}
    → eval ∘ ⟨ g × id ⟩ ≈ f
    → curry f ≈ g
  curry-unique {B = B} {C} = Bld.curry-unique (B ↝′ C)


  curry∘uncurry : ∀ {A B C} {f : A ⇒ B ↝ C}
    → curry (uncurry f) ≈ f
  curry∘uncurry {B = B} {C} = Bld.curry∘uncurry (B ↝′ C)


  uncurry∘curry : ∀ {A B C} {f : A × B ⇒ C}
    → uncurry (curry f) ≈ f
  uncurry∘curry {B = B} {C} = Bld.uncurry∘curry (B ↝′ C)


  curry∘curry : ∀ {A B C Y Z}
    → {f : (B ↝ C) × Y ⇒ Z} {g : A × B ⇒ C}
    → curry f ∘ curry g ≈ curry (f ∘ ⟨ curry g × id ⟩)
  curry∘curry {B = B} {C} {Y} {Z} = Bld.curry∘curry (B ↝′ C) (Y ↝′ Z)


  ↝-resp-≅ : ∀ {A A′ B B′}
    → A ≅ A′
    → B ≅ B′
    → (A ↝ B) ≅ (A′ ↝ B′)
  ↝-resp-≅ {A} {A′} {B} {B′} A≅A′ B≅B′
    = Bld.Exp-resp-≅ A≅A′ B≅B′ (A ↝′ B) (A′ ↝′ B′)


open Build public
