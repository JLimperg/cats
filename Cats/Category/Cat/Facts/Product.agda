{-# OPTIONS --without-K --safe #-}
module Cats.Category.Cat.Facts.Product where

open import Data.Bool using (true ; false)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Level using (_⊔_)

open import Cats.Category
open import Cats.Category.Cat as Cat using (Cat ; Functor ; _⇒_ ; _∘_ ; id ; _≈_)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Category.Product.Binary.Facts using (iso-intro)
open import Cats.Trans.Iso using (NatIso)

open Functor


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  private
    module C = Category C
    module D = Category D


  projl : (C × D) ⇒ C
  projl = record
      { fobj = proj₁
      ; fmap = proj₁
      ; fmap-resp = proj₁
      ; fmap-id = C.≈.refl
      ; fmap-∘ = C.≈.refl
      }


  projr : (C × D) ⇒ D
  projr = record
      { fobj = proj₂
      ; fmap = proj₂
      ; fmap-resp = proj₂
      ; fmap-id = D.≈.refl
      ; fmap-∘ = D.≈.refl
      }


  module _ {lo″ la″ l≈″} {X : Category lo″ la″ l≈″} where

    ⟨_,_⟩ : X ⇒ C → X ⇒ D → X ⇒ (C × D)
    ⟨ F , G ⟩ = record
        { fobj = λ x → fobj F x , fobj G x
        ; fmap = λ f → fmap F f , fmap G f
        ; fmap-resp = λ eq → fmap-resp F eq , fmap-resp G eq
        ; fmap-id = fmap-id F , fmap-id G
        ; fmap-∘ = fmap-∘ F , fmap-∘ G
        }


    module _ {F : X ⇒ C} {G : X ⇒ D} where

      ⟨,⟩-proj₁ : projl ∘ ⟨ F , G ⟩ ≈ F
      ⟨,⟩-proj₁ = record
          { iso = C.≅.refl
          ; forth-natural = C.≈.trans C.id-l (C.≈.sym C.id-r)
          }


      ⟨,⟩-proj₂ : projr ∘ ⟨ F , G ⟩ ≈ G
      ⟨,⟩-proj₂ = record
          { iso = D.≅.refl
          ; forth-natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
          }


      ⟨,⟩-unique : ∀ {H} → projl ∘ H ≈ F → projr ∘ H ≈ G → H ≈ ⟨ F , G ⟩
      ⟨,⟩-unique {H} eq₁ eq₂ = record
          { iso = iso-intro (iso eq₁) (iso eq₂)
          ; forth-natural = forth-natural eq₁ , forth-natural eq₂
          }
        where
          open NatIso


instance
  hasBinaryProducts : ∀ {lo la l≈} → HasBinaryProducts (Cat lo la l≈)
  hasBinaryProducts {lo} {la} {l≈} .HasBinaryProducts._×′_ C D
      = mkBinaryProduct projl projr isBinaryProduct
    where
      open module Catt = Category (Cat lo la l≈) using
        (IsBinaryProduct ; mkBinaryProduct ; ∃!-intro)
      module ≈ = Catt.≈

      isBinaryProduct : ∀ {C D : Category lo la l≈}
        → IsBinaryProduct (C × D) projl projr
      isBinaryProduct {C} {D} {X} F G = ∃!-intro
          ⟨ F , G ⟩
          (≈.sym (⟨,⟩-proj₁ {G = G}) , ≈.sym (⟨,⟩-proj₂ {F = F}))
          λ { (eq₁ , eq₂) → ≈.sym (⟨,⟩-unique (≈.sym eq₁) (≈.sym eq₂)) }


-- We get the following functors 'for free' from the above definition of
-- products in Cat, but those must have their domain and codomain category at
-- the same levels. The definitions below lift this restriction.


⟨_×_⟩ : ∀ {lo₁ la₁ l≈₁ lo₂ la₂ l≈₂ lo₃ la₃ l≈₃ lo₄ la₄ l≈₄}
  → {C : Category lo₁ la₁ l≈₁} {C′ : Category lo₂ la₂ l≈₂}
  → {D : Category lo₃ la₃ l≈₃} {D′ : Category lo₄ la₄ l≈₄}
  → C ⇒ C′ → D ⇒ D′ → (C × D) ⇒ (C′ × D′)
⟨ F × G ⟩ = ⟨ F ∘ projl , G ∘ projr ⟩


First : ∀ {lo₁ la₁ l≈₁ lo₂ la₂ l≈₂ lo₃ la₃ l≈₃}
  → {C : Category lo₁ la₁ l≈₁} {C′ : Category lo₂ la₂ l≈₂}
  → {D : Category lo₃ la₃ l≈₃}
  → C ⇒ C′ → (C × D) ⇒ (C′ × D)
First F = ⟨ F × id ⟩


Second : ∀ {lo₁ la₁ l≈₁ lo₂ la₂ l≈₂ lo₃ la₃ l≈₃}
  → {C : Category lo₁ la₁ l≈₁} {D : Category lo₂ la₂ l≈₂}
  → {D′ : Category lo₃ la₃ l≈₃}
  → D ⇒ D′ → (C × D) ⇒ (C × D′)
Second F = ⟨ id × F ⟩


Swap : ∀ {lo₁ la₁ l≈₁ lo₂ la₂ l≈₂}
  → {C : Category lo₁ la₁ l≈₁} {D : Category lo₂ la₂ l≈₂}
  → (C × D) ⇒ (D × C)
Swap = ⟨ projr , projl ⟩
