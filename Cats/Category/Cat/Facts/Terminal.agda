module Cats.Category.Cat.Facts.Terminal where

open import Cats.Category
open import Cats.Category.Cat using (Cat)
open import Cats.Category.One using (One)


instance
  hasTerminal : ∀ {lo la l≈} → HasTerminal (Cat lo la l≈)
  hasTerminal {lo} {la} {l≈} = record
      { One = One lo la l≈
      ; isTerminal = _
      }
