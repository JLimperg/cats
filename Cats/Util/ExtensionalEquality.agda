module Cats.Util.ExtensionalEquality where

open import Level
open import Relation.Binary using (Rel ; IsEquivalence)


infixr 4 _≈[_]_


_≈[_]_ : ∀ {a b l} {A : Set a} {B : Set b}
  → (A → B)
  → Rel B l
  → (A → B)
  → Set (a ⊔ l)
f ≈[ _≡_ ] g = ∀ x → f x ≡ g x


isEquivalence : ∀ {a b l} {A : Set a} {B : Set b} {_≡_ : Rel B l}
  → IsEquivalence _≡_
  → IsEquivalence {A = A → B} (_≈[ _≡_ ]_)
isEquivalence ≡-equiv = record
    { refl = λ _ → refl
    ; sym = λ eq x → sym (eq x)
    ; trans = λ eq₁ eq₂ x → trans (eq₁ x) (eq₂ x)
    }
  where open IsEquivalence ≡-equiv
