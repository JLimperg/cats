module Cats.Util.Conv where

open import Level


record Conv {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  infix 90 _↓
  field
    _↓ : (x : A) → B x

open Conv {{...}} public


Conv′ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Conv′ A B = Conv A (λ _ → B)
