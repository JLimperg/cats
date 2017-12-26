module Cats.Limit where

open import Level

open import Cats.Category
open import Cats.Category.Cones using
  (Cone ; Cones ; Conv-Cone-Obj ; Conv-⇒-→ ; cone-iso→obj-iso)
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
    Conv-Limit-Cone : Conv′ Limit (Cone D)
    Conv-Limit-Cone .Conv._↓ = Limit.cone


  unique : (l m : Limit) → l ↓ ≅ m ↓
  unique l m = terminal-unique (isTerminal l) (isTerminal m)


  obj-unique : (l m : Limit) → Apex (l ↓) Z.≅ Apex (m ↓)
  obj-unique l m = cone-iso→obj-iso _ (unique l m)
