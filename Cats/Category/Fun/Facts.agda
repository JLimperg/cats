module Cats.Category.Fun.Facts where

open import Cats.Category
open import Cats.Category.Cat using (_≈_)
open import Cats.Category.Fun using (Trans ; Fun ; ≈-intro ; ≈-elim)
open import Cats.Functor using (Functor)
open import Cats.Trans.Iso using (NatIso ; iso ; forth-natural ; back-natural)

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
      ; back-forth = ≈-intro (back-forth (iso i))
      ; forth-back = ≈-intro (forth-back (iso i))
      }
    where
      open NatIso


  ≅→NatIso : F ≅ G → NatIso F G
  ≅→NatIso i = record
      { iso = λ {c} → record
          { forth = component (forth i) c
          ; back = component (back i) c
          ; back-forth = ≈-elim (back-forth i)
          ; forth-back = ≈-elim (forth-back i)
          }
      ; forth-natural = natural (forth i)
      }


  ≈→≅ : F ≈ G → F ≅ G
  ≈→≅ eq = NatIso→≅ eq


  ≅→≈ : F ≅ G → F ≈ G
  ≅→≈ i = ≅→NatIso i
