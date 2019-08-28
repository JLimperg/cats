{-# OPTIONS --without-K --safe #-}
module Cats.Util.Function where

open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡

open import Function as Fun public using (id ; _on_)
open import Relation.Binary.Construct.On public
  renaming (isEquivalence to on-isEquivalence)


infixr 9 _∘_


_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → A → C
f ∘ g = f Fun.∘ g
