module Cats.Category.Constructions.Unique where

open import Data.Unit using (⊤)
open import Level

open import Cats.Category.Base
open import Cats.Util.Conv


module Build {lo la l≈} (Cat : Category lo la l≈) where

  open Category Cat


  IsUniqueSuchThat : ∀ {lp A B} → (A ⇒ B → Set lp) → A ⇒ B → Set (la ⊔ l≈ ⊔ lp)
  IsUniqueSuchThat P f = ∀ {g} → P g → f ≈ g


  IsUnique : ∀ {A B} → A ⇒ B → Set (la ⊔ l≈)
  IsUnique {A} {B} = IsUniqueSuchThat {A = A} {B} (λ _ → ⊤)


  IsUniqueSuchThat→≈ : ∀ {lp A B} {P : A ⇒ B → Set lp} {f}
    → IsUniqueSuchThat P f
    → ∀ {g h}
    → P g
    → P h
    → g ≈ h
  IsUniqueSuchThat→≈ unique Pg Ph = ≈.trans (≈.sym (unique Pg)) (unique Ph)


  record ∃!′ {lp A B} (P : A ⇒ B → Set lp) : Set (la ⊔ l≈ ⊔ lp) where
    constructor ∃!-intro
    field
      arr : A ⇒ B
      prop : P arr
      unique : IsUniqueSuchThat P arr


  instance
    HasArrow-∃! : ∀ {lp A B} {P : A ⇒ B → Set lp}
      → HasArrow (∃!′ P) lo la l≈
    HasArrow-∃! = record { Cat = Cat ; _⃗ = ∃!′.arr }


  syntax ∃!′ (λ f → P) = ∃![ f ] P


  ∃!″ : ∀ {lp A B} (P : A ⇒ B → Set lp) → Set (la ⊔ l≈ ⊔ lp)
  ∃!″ = ∃!′

  syntax ∃!″ {A = A} {B} (λ f → P) = ∃![ f ∈ A ⇒ B ] P


  ∃! : (A B : Obj) → Set (la ⊔ l≈)
  ∃! A B = ∃![ f ∈ A ⇒ B ] ⊤


  ∃!→≈ : ∀ {lp A B} {P : A ⇒ B → Set lp}
    → ∃!′ P
    → ∀ {g h}
    → P g
    → P h
    → g ≈ h
  ∃!→≈ (∃!-intro _ _ unique) = IsUniqueSuchThat→≈ unique


open Build public
