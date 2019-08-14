module Cats.Category.Constructions.Terminal where

open import Data.Product using (proj₁ ; proj₂)
open import Level

open import Cats.Category.Base

import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Constructions.Unique as Unique


module Build {lo la l≈} (Cat : Category lo la l≈) where

  open Category Cat
  open Iso.Build Cat
  open Unique.Build Cat


  IsTerminal : Obj → Set (lo ⊔ la ⊔ l≈)
  IsTerminal ⊤ = ∀ X → ∃! X ⊤


  record HasTerminal : Set (lo ⊔ la ⊔ l≈) where
    field
      ⊤ : Obj
      isTerminal : IsTerminal ⊤


    ! : ∀ X → X ⇒ ⊤
    ! X = ∃!′.arr (isTerminal X)


    !-unique : ∀ {X} (f : X ⇒ ⊤) → ! X ≈ f
    !-unique {X} f = ∃!′.unique (isTerminal X) _


    ⇒⊤-unique : ∀ {X} (f g : X ⇒ ⊤) → f ≈ g
    ⇒⊤-unique f g = ≈.trans (≈.sym (!-unique f)) (!-unique g)


    ⊤-unique : ∀ {X} → IsTerminal X → X ≅ ⊤
    ⊤-unique {X} term = record
      { forth = ! X
      ; back = term ⊤ .∃!′.arr
      ; back-forth = ≈.trans (≈.sym (term X .∃!′.unique _)) (term X .∃!′.unique _)
      ; forth-back = ⇒⊤-unique _ _
      }


  terminal-unique : ∀ {X Y} → IsTerminal X → IsTerminal Y → X ≅ Y
  terminal-unique X-term Y-term
    = HasTerminal.⊤-unique (record { isTerminal = Y-term }) X-term


open Build public using (HasTerminal)

private
  open module Build′ {lo la l≈} {C : Category lo la l≈}
    = Build C public using (IsTerminal ; terminal-unique)
