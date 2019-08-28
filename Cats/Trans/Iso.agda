{-# OPTIONS --without-K --safe #-}
module Cats.Trans.Iso where

open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Cats.Category.Base
open import Cats.Functor using (Functor)
open import Cats.Trans using (Trans ; component ; natural)

import Cats.Category.Constructions.Iso as Iso

open Functor
open Iso.Iso


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  private
    module C = Category C
    module D = Category D
    open module D≅ = Iso.Build D using (_≅_)
    module ≅ = D≅.≅
    open D.≈-Reasoning


  record NatIso (F G : Functor C D) : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′)
    where
    field
      iso : ∀ {c} → fobj F c ≅ fobj G c

      forth-natural : ∀ {c d} {f : c C.⇒ d}
        → forth iso D.∘ fmap F f D.≈ fmap G f D.∘ forth iso


    back-natural : ∀ {c d} {f : c C.⇒ d}
      → back iso D.∘ fmap G f D.≈ fmap F f D.∘ back iso
    back-natural {f = f} =
        begin
          back iso D.∘ fmap G f
        ≈⟨ D.∘-resp-r (D.≈.sym D.id-r) ⟩
          back iso D.∘ fmap G f D.∘ D.id
        ≈⟨ D.∘-resp-r (D.∘-resp-r (D.≈.sym (forth-back iso))) ⟩
          back iso D.∘ fmap G f D.∘ forth iso D.∘ back iso
        ≈⟨ D.∘-resp-r D.unassoc ⟩
          back iso D.∘ (fmap G f D.∘ forth iso) D.∘ back iso
        ≈⟨ D.∘-resp-r (D.∘-resp-l (D.≈.sym forth-natural)) ⟩
          back iso D.∘ (forth iso D.∘ fmap F f) D.∘ back iso
        ≈⟨ D.unassoc ⟩
          (back iso D.∘ (forth iso D.∘ fmap F f)) D.∘ back iso
        ≈⟨ D.∘-resp-l D.unassoc ⟩
          ((back iso D.∘ forth iso) D.∘ fmap F f) D.∘ back iso
        ≈⟨ D.assoc ⟩
          (back iso D.∘ (forth iso)) D.∘ fmap F f D.∘ back iso
        ≈⟨ D.∘-resp-l (back-forth iso) ⟩
          D.id D.∘ fmap F f D.∘ back iso
        ≈⟨ D.id-l ⟩
          fmap F f D.∘ back iso
        ∎


    Forth : Trans F G
    Forth = record
        { component = λ _ → forth iso
        ; natural = forth-natural
        }


    Back : Trans G F
    Back = record
        { component = λ _ → back iso
        ; natural = back-natural
        }


  open NatIso public


  id : ∀ {F} → NatIso F F
  id = record
      { iso = ≅.refl
      ; forth-natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
      }


  sym : ∀ {F G} → NatIso F G → NatIso G F
  sym θ = record
      { iso = ≅.sym (iso θ)
      ; forth-natural = back-natural θ
      }


  _∘_ : ∀ {F G H} → NatIso G H → NatIso F G → NatIso F H
  _∘_ {F} {G} {H} θ ι = record
      { iso = ≅.trans (iso ι) (iso θ)
      ; forth-natural = λ {_} {_} {f} →
          begin
            (forth (iso θ) D.∘ forth (iso ι)) D.∘ fmap F f
          ≈⟨ D.assoc ⟩
            forth (iso θ) D.∘ forth (iso ι) D.∘ fmap F f
          ≈⟨ D.∘-resp-r (forth-natural ι) ⟩
            forth (iso θ) D.∘ fmap G f D.∘ forth (iso ι)
          ≈⟨ D.unassoc ⟩
            (forth (iso θ) D.∘ fmap G f) D.∘ forth (iso ι)
          ≈⟨ D.∘-resp-l (forth-natural θ) ⟩
            (fmap H f D.∘ forth (iso θ)) D.∘ forth (iso ι)
          ≈⟨ D.assoc ⟩
            fmap H f D.∘ forth (iso θ) D.∘ forth (iso ι)
          ∎
      }
