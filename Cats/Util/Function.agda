module Cats.Util.Function where

open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡

open import Cats.Util.ExtensionalEquality.Propositional

open import Function as Fun public using (id ; _on_)
open import Relation.Binary.On public
  renaming (isEquivalence to on-isEquivalence)


_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → A → C
f ∘ g = f Fun.∘ g


module _ {a b} {A : Set a} {B : Set b} {f : A → B} where

  ∘-id-r : f ∘ id ≈ f
  ∘-id-r _ = ≡.refl


  ∘-id-l : id ∘ f ≈ f
  ∘-id-l _ = ≡.refl


∘-assoc : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  → (h : C → D) (g : B → C) (f : A → B)
  → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
∘-assoc _ _ _ _ = ≡.refl


∘-resp : ∀ {l} {A B C : Set l}
  → (_∘_ {A = A} {B} {C}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
∘-resp {x = f} {g} {h} {i} f≈g h≈i x = ≡.trans (≡.cong f (h≈i _)) (f≈g _)
