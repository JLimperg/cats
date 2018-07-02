module Cats.Functor.Representable where

open import Data.Product using (_×_ ; _,_)
open import Relation.Binary using (Setoid)

open import Cats.Bifunctor using (Bifunctor)
open import Cats.Category
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Category.Setoids as Setoids using (Setoids)
open import Cats.Util.Assoc using (assoc!)
open import Cats.Util.SetoidReasoning

import Relation.Binary.PropositionalEquality as ≡


module Build {lo la l≈} (C : Category lo la l≈) where

  open Category C renaming (Hom to Homset)
  open Setoids._⇒_ using (arr ; resp)

  private
    module S = Category (Setoids la l≈)

  fmap : ∀ {A B A′ B′} → (A′ ⇒ A) × (B ⇒ B′) → Homset A B S.⇒ Homset A′ B′
  fmap {A} {B} {A′} {B′} (f , g) = record
      { arr = λ h → g ∘ h ∘ f
      ; resp = λ h≈i → ∘-resp-r (∘-resp-l h≈i)
      }

  Hom : Bifunctor (C ᵒᵖ) C (Setoids la l≈)
  Hom = record
      { fobj = λ { (A , B) → Homset A B }
      ; fmap = fmap
      ; fmap-resp = λ where
          (f≈g , h≈i) x≈y → ∘-resp h≈i (∘-resp x≈y f≈g)
      ; fmap-id = λ where
          {A , B} {h} {i} h≈i → ≈.trans id-l (≈.trans id-r h≈i)
      ; fmap-∘ = λ where
          {A , B} {A′ , B′} {A″ , B″} {f , f′} {g , g′} {h} {i} h≈i →
            begin⟨ Homset A″ B″ ⟩
              f′ ∘ (g′ ∘ h ∘ g) ∘ f
            ≈⟨ assoc! C ⟩
              (f′ ∘ g′) ∘ h ∘ g ∘ f
            ≈⟨ ∘-resp-r (∘-resp-l h≈i) ⟩
              (f′ ∘ g′) ∘ i ∘ g ∘ f
            ∎
      }

open Build public using () renaming (Hom to Hom[_])
