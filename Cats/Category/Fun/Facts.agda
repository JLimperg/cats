module Cats.Category.Fun.Facts where

open import Cats.Category
open import Cats.Category.Fun using (Trans ; Fun)
open import Cats.Functor using (Functor)
open import Cats.Util.Assoc using (assoc!)

open import Level using (_⊔_)

import Cats.Category.Constructions.Iso as Iso

open Functor
open Trans
open Iso.Build._≅_


record NatIso {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈}
  {D : Category lo′ la′ l≈′}
  (F G : Functor C D)
  : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′)
  where
  private
    module C = Category C
    module D = Category D
    open D.≈-Reasoning

  field
    iso : ∀ C → fobj F C D.≅ fobj G C

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


module _ {lo la l≈} {C D : Category lo la l≈} {F G : Functor C D} where

  open Category (Fun C D) using (_≅_)


  NatIso→≅ : NatIso F G → F ≅ G
  NatIso→≅ i = record
      { forth = record
          { component = λ c → forth (NatIso.iso i c)
          ; natural = NatIso.forth-natural i
          }
      ; back = record
          { component = λ c → back (NatIso.iso i c)
          ; natural = NatIso.back-natural i
          }
      ; back-forth = λ c → back-forth (NatIso.iso i c)
      ; forth-back = λ c → forth-back (NatIso.iso i c)
      }


  ≅→NatIso : F ≅ G → NatIso F G
  ≅→NatIso i = record
      { iso = λ c → record
          { forth = component (forth i) c
          ; back = component (back i) c
          ; back-forth = back-forth i c
          ; forth-back = forth-back i c
          }
      ; forth-natural = natural (forth i)
      }
