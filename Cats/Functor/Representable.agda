module Cats.Functor.Representable where

open import Data.Product using (_×_ ; _,_)
open import Relation.Binary using (Setoid)

open import Cats.Bifunctor using (Bifunctor)
open import Cats.Category
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Category.Setoids as Setoids using (Setoids ; ≈-intro)
open import Cats.Util.Simp using (simp!)

import Relation.Binary.PropositionalEquality as ≡

import Cats.Util.SetoidReasoning as SetoidReasoning


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
          (f≈g , h≈i) → ≈-intro λ x≈y → ∘-resp h≈i (∘-resp x≈y f≈g)
      ; fmap-id = ≈-intro λ x≈y → ≈.trans id-l (≈.trans id-r x≈y)
      ; fmap-∘ = λ where
          {A , B} {A′ , B′} {A″ , B″} {f , f′} {g , g′} → ≈-intro λ {x} {y} x≈y →
            let open SetoidReasoning (Homset A″ B″) in
            begin
              f′ ∘ (g′ ∘ x ∘ g) ∘ f
            ≈⟨ simp! C ⟩
              (f′ ∘ g′) ∘ x ∘ g ∘ f
            ≈⟨ ∘-resp-r (∘-resp-l x≈y) ⟩
              (f′ ∘ g′) ∘ y ∘ g ∘ f
            ∎
      }

open Build public using () renaming (Hom to Hom[_])
