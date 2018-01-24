module Cats.Limit where

open import Level

open import Cats.Category.Base
open import Cats.Category.Cones using
  (Cone ; Cones ; HasObj-Cone ; HasArrow-⇒ ; cone-iso→obj-iso ; apFunctor)
open import Cats.Functor using (Functor)
open import Cats.Util.Conv

import Cats.Category.Constructions.Terminal as Terminal
import Cats.Category.Constructions.Iso as Iso


module _ {lo la l≈ lo′ la′ l≈′}
  {J : Category lo la l≈}
  {Z : Category lo′ la′ l≈′}
  where

  IsLimit : {D : Functor J Z} → Cone D → Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′)
  IsLimit {D} = Terminal.Build.IsTerminal (Cones D)


  record Limit (D : Functor J Z) : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) where
    open Category (Cones D)
    field
      cone : Cone D
      isLimit : IsLimit cone


  instance
    HasObj-Limit : ∀ D → HasObj (Limit D) _ _ _
    HasObj-Limit D = record { Cat = Cones D ; _ᴼ = Limit.cone }


  module _ {D : Functor J Z} where

    open Iso.Build (Cones D) using (_≅_)
    open Iso.Build Z using () renaming (_≅_ to _≅Z_)
    open Limit using (isLimit)


    unique : (l m : Limit D) → l ᴼ ≅ m ᴼ
    unique l m = Terminal.Build.terminal-unique (Cones D) (isLimit l) (isLimit m)


    obj-unique : (l m : Limit D) → l ᴼ ᴼ ≅Z m ᴼ ᴼ
    obj-unique l m = cone-iso→obj-iso _ (unique l m)


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈}
  {D : Category lo′ la′ l≈′}
  where

  preservesLimits : (lo″ la″ l≈″ : Level) → (F : Functor C D) → Set _
  preservesLimits lo″ la″ l≈″ F
      = {J : Category lo″ la″ l≈″}
      → {D : Functor J C}
      → {c : Cone D}
      → IsLimit c
      → IsLimit (apFunctor F c)
