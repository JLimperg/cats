open import Relation.Binary using (Setoid)

module Cats.Util.SetoidReasoning {c ℓ} (S : Setoid c ℓ) where

open import Relation.Binary.Reasoning.Setoid S public
-- We can't use Relation.Binary.Reasoning.MultiSetoid due to
-- https://github.com/agda/agda-stdlib/issues/715

open Setoid S


triangle :
  ∀ m {x y}
  → x ≈ m
  → y ≈ m
  → x ≈ y
triangle m x≈m y≈m = trans x≈m (sym y≈m)
