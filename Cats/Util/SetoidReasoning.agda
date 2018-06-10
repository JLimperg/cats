module Cats.Util.SetoidReasoning where

open import Relation.Binary.SetoidReasoning public

open import Relation.Binary using (Setoid)
open import Relation.Binary.EqReasoning as EqR using (_IsRelatedTo_)


infixr 2 _≡⟨⟩_


_≡⟨⟩_ : ∀ {c l} {S : Setoid  c l} → ∀ x {y} → _IsRelatedTo_ S x y → _IsRelatedTo_ S x y
_≡⟨⟩_ {S = S} = EqR._≡⟨⟩_ S


triangle : ∀ {l l′} (S : Setoid l l′) →
  let open Setoid S in
  ∀ m {x y}
  → x ≈ m
  → y ≈ m
  → x ≈ y
triangle S m x≈m y≈m = trans x≈m (sym y≈m)
  where
    open Setoid S
