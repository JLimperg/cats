module Cats.Trans.Iso where

open import Level using (_⊔_)

open import Cats.Category.Base
open import Cats.Functor using (Functor)
open import Cats.Util.Assoc using (assoc!)
open import Cats.Trans using (Trans ; component ; natural)

import Cats.Category.Constructions.Iso as Iso

open Functor
open Iso.Build._≅_


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
      iso : ∀ C → fobj F C ≅ fobj G C

      forth-natural : ∀ {A B} {f : A C.⇒ B}
        → forth (iso B) D.∘ fmap F f D.≈ fmap G f D.∘ forth (iso A)


    back-natural : ∀ {A B} {f : A C.⇒ B}
      → back (iso B) D.∘ fmap G f D.≈ fmap F f D.∘ back (iso A)
    back-natural {A} {B} {f} =
        begin
          back (iso B) D.∘ fmap G f
        ≈⟨ D.∘-resp-r (D.≈.sym D.id-r) ⟩
          back (iso B) D.∘ fmap G f D.∘ D.id
        ≈⟨ D.∘-resp-r (D.∘-resp-r (D.≈.sym (forth-back (iso A)))) ⟩
          back (iso B) D.∘ fmap G f D.∘ forth (iso A) D.∘ back (iso A)
        ≈⟨ assoc! D ⟩
          back (iso B) D.∘ (fmap G f D.∘ forth (iso A)) D.∘ back (iso A)
        ≈⟨ D.∘-resp-r (D.∘-resp-l (D.≈.sym forth-natural)) ⟩
          back (iso B) D.∘ (forth (iso B) D.∘ fmap F f) D.∘ back (iso A)
        ≈⟨ assoc! D ⟩
          (back (iso B) D.∘ (forth (iso B))) D.∘ fmap F f D.∘ back (iso A)
        ≈⟨ D.∘-resp-l (back-forth (iso B)) ⟩
          D.id D.∘ fmap F f D.∘ back (iso A)
        ≈⟨ D.id-l ⟩
          fmap F f D.∘ back (iso A)
        ∎


    Forth : Trans F G
    Forth = record
        { component = λ c → forth (iso c)
        ; natural = forth-natural
        }


    Back : Trans G F
    Back = record
        { component = λ c → back (iso c)
        ; natural = back-natural
        }

  open NatIso public


  id : ∀ {F} → NatIso F F
  id = record
      { iso = λ _ → ≅.refl
      ; forth-natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
      }


  sym : ∀ {F G} → NatIso F G → NatIso G F
  sym θ = record
      { iso = λ c → ≅.sym (iso θ c)
      ; forth-natural = back-natural θ
      }


  _∘_ : ∀ {F G H} → NatIso G H → NatIso F G → NatIso F H
  _∘_ {F} {G} {H} θ ι = record
      { iso = λ c → ≅.trans (iso ι c) (iso θ c)
      ; forth-natural = λ {c} {d} {f} →
          begin
            (forth (iso θ d) D.∘ forth (iso ι d)) D.∘ fmap F f
          ≈⟨ D.assoc ⟩
            forth (iso θ d) D.∘ forth (iso ι d) D.∘ fmap F f
          ≈⟨ D.∘-resp-r (forth-natural ι) ⟩
            forth (iso θ d) D.∘ fmap G f D.∘ forth (iso ι c)
          ≈⟨ D.unassoc ⟩
            (forth (iso θ d) D.∘ fmap G f) D.∘ forth (iso ι c)
          ≈⟨ D.∘-resp-l (forth-natural θ) ⟩
            (fmap H f D.∘ forth (iso θ c)) D.∘ forth (iso ι c)
          ≈⟨ D.assoc ⟩
            fmap H f D.∘ forth (iso θ c) D.∘ forth (iso ι c)
          ∎
      }
