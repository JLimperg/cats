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
  IsTerminal One = ∀ X → ∃! X One


  terminal→id-unique : ∀ {A} → IsTerminal A → IsUnique (id {A})
  terminal→id-unique {A} term id′ with term A
  ... | ∃!-intro id″ _ id″-uniq = ≈.trans (≈.sym (id″-uniq _)) (id″-uniq _)


  terminal-unique : ∀ {A B} → IsTerminal A → IsTerminal B → A ≅ B
  terminal-unique {A} {B} A-term B-term = record
      { forth = ∃!′.arr (B-term A)
      ; back = ∃!′.arr (A-term B)
      ; back-forth = ≈.sym (terminal→id-unique A-term _)
      ; forth-back = ≈.sym (terminal→id-unique B-term _)
      }


  X⇒Terminal-unique : ∀ {One} → IsTerminal One → ∀ {X} {f g : X ⇒ One} → f ≈ g
  X⇒Terminal-unique term {X} {f} {g} with term X
  ... | ∃!-intro x _ x-uniq = ≈.trans (≈.sym (x-uniq _)) (x-uniq _)


  record HasTerminal : Set (lo ⊔ la ⊔ l≈) where
    field
      One : Obj
      isTerminal : IsTerminal One


open Build public
