module Cats.Util.SetoidReasoning where

open import Relation.Binary.Reasoning.MultiSetoid public

open import Relation.Binary using (Setoid)

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S

  triangle :
    ∀ m {x y}
    → x ≈ m
    → y ≈ m
    → x ≈ y
  triangle m x≈m y≈m = trans x≈m (sym y≈m)
