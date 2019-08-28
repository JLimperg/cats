{-# OPTIONS --without-K --safe #-}
module Cats.Category.Constructions.Initial where

open import Data.Product using (proj₁ ; proj₂)
open import Level

open import Cats.Category.Base

import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Constructions.Unique as Unique


module Build {lo la l≈} (Cat : Category lo la l≈) where

  open Category Cat
  open Iso.Build Cat
  open Unique.Build Cat


  IsInitial : Obj → Set (lo ⊔ la ⊔ l≈)
  IsInitial ⊥ = ∀ X → ∃! ⊥ X


  record HasInitial : Set (lo ⊔ la ⊔ l≈) where
    field
      ⊥ : Obj
      isInitial : IsInitial ⊥


    ¡ : ∀ X → ⊥ ⇒ X
    ¡ X = ∃!′.arr (isInitial X)


    ¡-unique : ∀ {X} (f : ⊥ ⇒ X) → ¡ X ≈ f
    ¡-unique {X} f = ∃!′.unique (isInitial X) _


    ⊥⇒-unique : ∀ {X} (f g : ⊥ ⇒ X) → f ≈ g
    ⊥⇒-unique f g = ≈.trans (≈.sym (¡-unique f)) (¡-unique g)


    ⊥-unique : ∀ {X} → IsInitial X → X ≅ ⊥
    ⊥-unique {X} init = record
      { forth = init ⊥ .∃!′.arr
      ; back = ¡ X
      ; back-forth = ≈.trans (≈.sym (init X .∃!′.unique _)) (init X .∃!′.unique _)
      ; forth-back = ⊥⇒-unique _ _
      }


  initial-unique : ∀ {X Y} → IsInitial X → IsInitial Y → X ≅ Y
  initial-unique X-init Y-init
    = HasInitial.⊥-unique (record { isInitial = Y-init }) X-init


open Build public using (HasInitial)

private
  open module Build′ {lo la l≈} {C : Category lo la l≈}
    = Build C public using (IsInitial ; initial-unique)
