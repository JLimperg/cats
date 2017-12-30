module Cats.Limit where

open import Level

open import Cats.Category
open import Cats.Category.Cones using
  (Cone ; Cones ; HasObj-Cone ; HasArrow-⇒ ; cone-iso→obj-iso)
open import Cats.Functor
open import Cats.Util.Conv


module _ {lo la l≈ lo′ la′ l≈′}
  {J : Category lo la l≈}
  {Z : Category lo′ la′ l≈′}
  (D : Functor J Z)
  where

  open Category (Cones D)
  open Cone using (Apex)


  private
    module J = Category J
    module Z = Category Z
    module D = Functor D


  record Limit : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) where
    field
      cone : Cone D
      isTerminal : IsTerminal cone

  open Limit using (isTerminal)


  instance
    HasObj-Limit : HasObj Limit _ _ _
    HasObj-Limit = record { Cat = Cones D ; _ᴼ = Limit.cone }


  unique : (l m : Limit) → l ᴼ ≅ m ᴼ
  unique l m = terminal-unique (isTerminal l) (isTerminal m)


  obj-unique : (l m : Limit) → l ᴼ ᴼ Z.≅ m ᴼ ᴼ
  obj-unique l m = cone-iso→obj-iso _ (unique l m)
