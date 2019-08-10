module Cats.Category.Sets.Facts.Initial where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Level using (Lift ; lift ; lower)

open import Cats.Category
open import Cats.Category.Sets using (Sets)


instance
  hasInitial : ∀ {l} → HasInitial (Sets l)
  hasInitial = record
    { Zero = Lift _ ⊥
    ; isInitial = λ X → record
      { arr = λ()
      ; prop = _
      ; unique = λ { _ () }
      }
    }
