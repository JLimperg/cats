module Cats.Util.Monad where

open import Category.Monad public

open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Level using (Lift ; lift)

open RawMonad {{...}} public


private
  _<*>_ = _⊛_


module _ {f} {M : Set f → Set f} {{_ : RawMonad M}} where

  sequence : ∀ {A} → List (M A) → M (List A)
  sequence [] = return []
  sequence (mx ∷ mxs) = ⦇ mx ∷ sequence mxs ⦈


  void : ∀ {A} → M A → M (Lift ⊤)
  void m = m >>= λ _ → return _


  mapM : ∀ {a} {A : Set a} {B} → (A → M B) → List A → M (List B)
  mapM f = sequence ∘ map f


  mapM′ : ∀ {a} {A : Set a} {B} → (A → M B) → List A → M (Lift ⊤)
  mapM′ f = void ∘ mapM f
