module Cats.Category.Cat.Facts.Initial where

open import Cats.Category
open import Cats.Category.Cat using (Cat)
open import Cats.Category.Zero using (Zero)
open import Cats.Functor


module _ {lo la l≈} where

  open Category (Cat lo la l≈)


  Zero-Initial : IsInitial (Zero lo la l≈)
  Zero-Initial X = ∃!-intro f _ f-Unique
    where
      f : Functor (Zero lo la l≈) X
      f = record
          { fobj = λ()
          ; fmap = λ{}
          ; fmap-resp = λ{}
          ; fmap-id = λ{}
          ; fmap-∘ = λ{}
          }

      f-Unique : IsUnique f
      f-Unique f′ = record
          { iso = λ{}
          ; fmap-≈ = λ{}
          }


instance
  hasInitial : ∀ lo la l≈ → HasInitial (Cat lo la l≈)
  hasInitial lo la l≈ = record
      { Zero = Zero lo la l≈
      ; isInitial = Zero-Initial
      }
