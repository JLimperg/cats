module Cats.Functor.Representable where

open import Relation.Binary using (Setoid)

open import Cats.Category
open import Cats.Category.Setoids as Setoids using (Setoids)
open import Cats.Functor using (Functor)


module _ {lo la l≈} where

  Hom[_] : (C : Category lo la l≈) → Category.Obj C → Functor C (Setoids la l≈)
  Hom[ C ] X = record
      { fobj = fobj
      ; fmap = fmap
      ; fmap-resp = λ f≈g h≈i → ∘-resp f≈g h≈i
      ; fmap-id = trans id-l
      ; fmap-∘ = λ f g x≈y
          → trans assoc (resp (fmap f) (resp (fmap g) x≈y))
      }
    module Hom where
      open Category C renaming (Hom to Homset)
      open Category (Setoids la l≈) using () renaming (_⇒_ to _⇒′_)
      open Setoids.Build._⇒_ using (resp)

      fobj : Obj → Setoid la l≈
      fobj A = Homset X A

      private
        open module S {A} = Setoid (fobj A) using (trans)

      fmap : ∀ {A B} → A ⇒ B → fobj A ⇒′ fobj B
      fmap f = record
          { arr = λ g → f ∘ g
          ; resp = ∘-resp-r
          }
