{-# OPTIONS --without-K --safe #-}
module Cats.Category.Sets where

open import Data.Product using (Σ ; _×_ ; proj₁ ; proj₂)
open import Level
open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Category.Base
open import Cats.Util.Function using (id ; _∘_)


module _ {l} {A B : Set l} where

  infixr 4 _≈_


  _≈_ : (f g : A → B) → Set l
  f ≈ g = ∀ x → f x ≡ g x


  equiv : IsEquivalence _≈_
  equiv = record
      { refl = λ x → ≡.refl
      ; sym = λ eq x → ≡.sym (eq x)
      ; trans = λ eq₁ eq₂ x → ≡.trans (eq₁ x) (eq₂ x)
      }


Sets : ∀ l → Category (suc l) l l
Sets l = record
    { Obj = Set l
    ; _⇒_ = λ A B → A → B
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = _∘_
    ; equiv = equiv
    ; ∘-resp = λ {_} {_} {_} {f} eq₁ eq₂ x
        → ≡.trans (≡.cong f (eq₂ _)) (eq₁ _)
    ; id-r = λ _ → ≡.refl
    ; id-l = λ _ → ≡.refl
    ; assoc = λ _ → ≡.refl
    }
