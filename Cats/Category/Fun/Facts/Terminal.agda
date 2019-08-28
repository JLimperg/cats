{-# OPTIONS --without-K --safe #-}
module Cats.Category.Fun.Facts.Terminal where

open import Cats.Category.Base
open import Cats.Category.Constructions.Terminal using (HasTerminal)
open import Cats.Category.Fun using (_↝_ ; ≈-intro)
open import Cats.Functor using (Functor)
open import Cats.Functor.Const using (Const)

open Functor


instance
  hasTerminal : ∀ {lo la l≈ lo′ la′ l≈′}
    → {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
    → {{_ : HasTerminal D}}
    → HasTerminal (C ↝ D)
  hasTerminal {C = C} {D = D} {{D⊤}} = record
    { ⊤ = Const C ⊤
    ; isTerminal = λ X → record
      { arr = record
        { component = λ c → ! (fobj X c)
        ; natural = λ {c} {d} {f} → ⇒⊤-unique _ _
        }
      ; unique = λ _ → ≈-intro (⇒⊤-unique _ _)
      }
    }
    where
      open HasTerminal D⊤
