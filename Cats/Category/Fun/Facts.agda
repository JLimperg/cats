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
      { forth = Forth i
      ; back = Back i
      ; back-forth = λ c → back-forth (iso i)
      ; forth-back = λ c → forth-back (iso i)
      }
    where
      open NatIso


  ≅→NatIso : F ≅ G → NatIso F G
  ≅→NatIso i = record
      { iso = λ {c} → record
          { forth = component (forth i) c
          ; back = component (back i) c
          ; back-forth = back-forth i c
          ; forth-back = forth-back i c
          }
      ; forth-natural = natural (forth i)
      }


  ≈→≅ : F ≈ G → F ≅ G
  ≈→≅ eq = NatIso→≅ eq


  ≅→≈ : F ≅ G → F ≈ G
  ≅→≈ i = ≅→NatIso i
