module Cats.Category.Fun.Facts.Iso where

open import Cats.Category
open import Cats.Category.Cat using (_≈_)
open import Cats.Category.Fun using (Fun ; Trans ; ≈-intro ; ≈-elim)
open import Cats.Functor using (Functor)
open import Cats.Trans.Iso using (NatIso)

import Cats.Category.Constructions.Iso as Iso

open NatIso
open Trans
open Iso.Iso


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  {F G : Functor C D}
  where

  open Category (Fun C D) using (_≅_)


  ≈→≅ : F ≈ G → F ≅ G
  ≈→≅ i = record
    { forth = Forth i
    ; back = Back i
    ; back-forth = ≈-intro (back-forth (iso i))
    ; forth-back = ≈-intro (forth-back (iso i))
    }


  ≅→≈ : F ≅ G → F ≈ G
  ≅→≈ i = record
    { iso = λ {c} → record
      { forth = component (forth i) c
      ; back = component (back i) c
      ; back-forth = ≈-elim (back-forth i)
      ; forth-back = ≈-elim (forth-back i)
      }
    ; forth-natural = natural (forth i)
    }
