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
  IsInitial Zero = ∀ X → ∃! Zero X


  initial→id-unique : ∀ {A} → IsInitial A → IsUnique (id {A})
  initial→id-unique {A} init id′ with init A
  ... | ∃!-intro id″ _ id″-uniq = ≈.trans (≈.sym (id″-uniq _)) (id″-uniq _)


  initial-unique : ∀ {A B} → IsInitial A → IsInitial B → A ≅ B
  initial-unique {A} {B} A-init B-init = record
      { forth = ∃!′.arr (A-init B)
      ; back = ∃!′.arr (B-init A)
      ; back-forth = ≈.sym (initial→id-unique A-init _)
      ; forth-back = ≈.sym (initial→id-unique B-init _)
      }


  Initial⇒X-unique : ∀ {Zero} → IsInitial Zero → ∀ {X} {f g : Zero ⇒ X} → f ≈ g
  Initial⇒X-unique init {X} {f} {g} with init X
  ... | ∃!-intro x _ x-uniq = ≈.trans (≈.sym (x-uniq _)) (x-uniq _)
