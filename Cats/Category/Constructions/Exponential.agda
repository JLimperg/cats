module Cats.Category.Constructions.Exponential where

open import Level

open import Cats.Category.Base
open import Cats.Category.Constructions.Product as Product using
  (HasBinaryProducts)
open import Cats.Util.Conv

import Cats.Category.Constructions.Unique as Unique


module Build {lo la l≈}
  (Cat : Category lo la l≈)
  {{hasBinaryProducts : HasBinaryProducts Cat}}
  where

  open Category Cat
  open Unique.Build Cat
  open HasBinaryProducts hasBinaryProducts


  record Exp (B C : Obj) : Set (lo ⊔ la ⊔ l≈) where
    field
      Cᴮ : Obj
      eval : Cᴮ × B ⇒ C
      curry : ∀ {A} (f : A × B ⇒ C)
        → ∃![ f̃ ∈ A ⇒ Cᴮ ] (eval ∘ ⟨ f̃ × id ⟩ ≈ f)


  instance HasObj-Exp : ∀ {B C} → HasObj (Exp B C) lo la l≈
  HasObj-Exp = record { Cat = Cat ; _ᴼ = Exp.Cᴮ }


  module _ {B C} (Cᴮ : Exp B C) where

    open Exp Cᴮ using (eval ; curry)


    uncurry : ∀ {A} → A ⇒ Cᴮ ᴼ → A × B ⇒ C
    uncurry f = eval ∘ ⟨ f × id ⟩


    curry∘uncurry : ∀ {A} {f : A ⇒ Cᴮ ᴼ}
      → curry (uncurry f) ⃗ ≈ f
    curry∘uncurry {f = f} = ∃!′.unique (curry (uncurry f)) ≈.refl


    uncurry∘curry : ∀ {A} {f : A × B ⇒ C}
      → uncurry (curry f ⃗) ≈ f
    uncurry∘curry {f = f} = ∃!′.prop (curry f)


  open Exp public using (eval ; curry)


record HasExponentials {lo la l≈}
  (Cat : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈)
  where
  private open module Bld = Build Cat using (Exp)
  open Category Cat
  open Unique.Build Cat

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
  curry {B = B} {C} f = Bld.curry (B ↝′ C) f ⃗


  uncurry : ∀ {A B C} → A ⇒ B ↝ C → A × B ⇒ C
  uncurry {B = B} {C} = Bld.uncurry (B ↝′ C)


  eval-curry : ∀ {A B C} {f : A × B ⇒ C}
    → eval ∘ ⟨ curry f × id ⟩ ≈ f
  eval-curry {B = B} {C} {f} = ∃!′.prop (Bld.curry (B ↝′ C) f)


  curry∘uncurry : ∀ {A B C} {f : A ⇒ B ↝ C}
    → curry (uncurry f) ≈ f
  curry∘uncurry {B = B} {C} = Bld.curry∘uncurry (B ↝′ C)


  uncurry∘curry : ∀ {A B C} {f : A × B ⇒ C}
    → uncurry (curry f) ≈ f
  uncurry∘curry {B = B} {C} = Bld.uncurry∘curry (B ↝′ C)
