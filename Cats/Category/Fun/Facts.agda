module Cats.Category.Fun.Facts where

open import Cats.Category
open import Cats.Category.Cat using (_≈_)
open import Cats.Category.Fun using (Trans ; Fun)
open import Cats.Functor using (Functor)
open import Cats.Trans.Iso using (NatIso ; iso ; forth-natural ; back-natural)
open import Cats.Util.Assoc using (assoc!)

open import Level using (_⊔_)

open Functor
open Trans
open Category._≅_


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈}
  {D : Category lo′ la′ l≈′}
  {F G : Functor C D}
  where

  private
    module C = Category C
    module D = Category D
    open D.≈-Reasoning
    open Category (Fun C D) using (_≅_)


  NatIso→≅ : NatIso F G → F ≅ G
  NatIso→≅ i = record
      { forth = record
          { component = λ c → forth (iso i c)
          ; natural = forth-natural i
          }
      ; back = record
          { component = λ c → back (iso i c)
          ; natural = back-natural i
          }
      ; back-forth = λ c → back-forth (iso i c)
      ; forth-back = λ c → forth-back (iso i c)
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


  ≈→≅ : F ≈ G → F ≅ G
  ≈→≅ record { iso = i ; fmap-≈ = fmap-≈ } = NatIso→≅ record
      { iso = λ _ → i
      ; forth-natural = λ {c} {d} {f} →
          begin
            forth i D.∘ fmap F f
          ≈⟨ D.∘-resp-r (fmap-≈ f) ⟩
            forth i D.∘ back i D.∘ fmap G f D.∘ forth i
          ≈⟨ assoc! D ⟩
            (forth i D.∘ back i) D.∘ fmap G f D.∘ forth i
          ≈⟨ D.∘-resp-l (forth-back i) ⟩
            D.id D.∘ fmap G f D.∘ forth i
          ≈⟨ D.id-l ⟩
            fmap G f D.∘ forth i
          ∎
      }


  ≅→≈ : F ≅ G → F ≈ G
  ≅→≈ F≅G with ≅→NatIso F≅G
  ... | ni@record { iso = i } = record
      { iso = λ {x} → i x
      ; fmap-≈ = λ {A} {B} f → D.≈.sym (
          begin
            back (i B) D.∘ fmap G f D.∘ forth (i A)
          ≈⟨ assoc! D ⟩
            (back (i B) D.∘ fmap G f) D.∘ forth (i A)
          ≈⟨ D.∘-resp-l (back-natural ni) ⟩
            (fmap F f D.∘ back (i A)) D.∘ forth (i A)
          ≈⟨ assoc! D ⟩
            fmap F f D.∘ back (i A) D.∘ forth (i A)
          ≈⟨ D.∘-resp-r (back-forth (i A))  ⟩
            fmap F f D.∘ D.id
          ≈⟨ D.id-r ⟩
            fmap F f
          ∎
        )
      }
