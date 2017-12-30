module Cats.Util.Conv where

open import Level

open import Cats.Category.Base


module _ {x} (X : Set x) where

  record HasObj lo la l≈ : Set (x ⊔ suc (lo ⊔ la ⊔ l≈))
    where
    infix 90 _ᴼ
    field
      Cat : Category lo la l≈

    open Category Cat

    field
      _ᴼ : X → Obj

  open HasObj {{...}} public using (_ᴼ)


  record HasArrow lo la l≈ : Set (x ⊔ suc (lo ⊔ la ⊔ l≈))
    where
    infixr 90 _⃗
    field
      Cat : Category lo la l≈

    open Category Cat using (Obj ; _⇒_)

    field
      {A B} : X → Obj
      _⃗ : (x : X) → A x ⇒ B x

  open HasArrow {{...}} public using (_⃗)
