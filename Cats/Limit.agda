module Cats.Limit where

open import Level

open import Cats.Category
open import Cats.Category.Cones using
  (Cone ; Cones ; HasObj-Cone ; HasArrow-⇒ ; cone-iso→obj-iso ; apFunctor)
open import Cats.Functor
open import Cats.Util.Conv


module _ {lo la l≈ lo′ la′ l≈′}
  {J : Category lo la l≈}
  {Z : Category lo′ la′ l≈′}
  where

  IsLimit : {D : Functor J Z} → Cone D → Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′)
  IsLimit {D} = Category.IsTerminal (Cones D)


  record Limit (D : Functor J Z) : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) where
    open Category (Cones D)
    field
      cone : Cone D
      isLimit : IsLimit cone


  instance
    HasObj-Limit : ∀ D → HasObj (Limit D) _ _ _
    HasObj-Limit D = record { Cat = Cones D ; _ᴼ = Limit.cone }


  module _ {D : Functor J Z} where

    open Category (Cones D) using (_≅_ ; terminal-unique)
    open Limit using (isLimit)

    private
      module Z = Category Z


    unique : (l m : Limit D) → l ᴼ ≅ m ᴼ
    unique l m = terminal-unique (isLimit l) (isLimit m)


    obj-unique : (l m : Limit D) → l ᴼ ᴼ Z.≅ m ᴼ ᴼ
    obj-unique l m = cone-iso→obj-iso _ (unique l m)


module _ {lo la l≈} {C D : Category lo la l≈} where

  preservesLimits : (F : Functor C D) → Set (suc (lo ⊔ la ⊔ l≈))
  preservesLimits F
      = {J : Category lo la l≈}
      → {D : Functor J C}
      → {c : Cone D}
      → IsLimit c
      → IsLimit (apFunctor F c)
