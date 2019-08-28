{-# OPTIONS --without-K --safe #-}
module Cats.End where

open import Level using (_⊔_)

open import Cats.Category
open import Cats.Category.Wedges using (Wedge ; Wedges)
open import Cats.Profunctor


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  IsEnd : {F : Profunctor C C D} → Wedge F → Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′)
  IsEnd {F} = Wdg.IsTerminal
    where
      module Wdg = Category (Wedges F)


  record End (F : Profunctor C C D) : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) where
    field
      wedge : Wedge F
      isEnd : IsEnd wedge
