{-# OPTIONS --without-K --safe #-}
module Cats.Util.SetoidReasoning where

open import Relation.Binary.Reasoning.MultiSetoid public

open import Relation.Binary using (Setoid)
open import Relation.Binary.Reasoning.Syntax using (module ≡-syntax)

-- Since stdlib 2.0, MultiSetoid no longer exports the _≡⟨_⟩_ family.
module _ {c ℓ} {S : Setoid c ℓ} where
  open ≡-syntax (IsRelatedTo S) (≡-go S) public

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S

  triangle :
    ∀ m {x y}
    → x ≈ m
    → y ≈ m
    → x ≈ y
  triangle m x≈m y≈m = trans x≈m (sym y≈m)
