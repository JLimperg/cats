module Cats.Category.Product.Binary.Facts where

open import Cats.Category
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Functor
open import Cats.Util.Logic.Constructive using (_∧_ ; _,_ ; ∧-eliml ; ∧-elimr)


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈}
  {D : Category lo′ la′ l≈′}
  where

  private
    module C = Category C
    module D = Category D
    module × = Category (C × D)

  open Category._≅_


  iso-intro : ∀ {A A′ B B′} → A C.≅ A′ → B D.≅ B′ → (A , B) ×.≅ (A′ , B′)
  iso-intro f g = record
      { forth = forth f , forth g
      ; back = back f , back g
      ; back-forth = back-forth f , back-forth g
      ; forth-back = forth-back f , forth-back g
      }


  iso-elim : ∀ {A A′ B B′} → (A , B) ×.≅ (A′ , B′) → A C.≅ A′ ∧ B D.≅ B′
  iso-elim f
      = record
      { forth = ∧-eliml (forth f)
      ; back = ∧-eliml (back f)
      ; back-forth = ∧-eliml (back-forth f)
      ; forth-back = ∧-eliml (forth-back f)
      }
      , record
      { forth = ∧-elimr (forth f)
      ; back = ∧-elimr (back f)
      ; back-forth = ∧-elimr (back-forth f)
      ; forth-back = ∧-elimr (forth-back f)
      }


  proj₁ : Functor (C × D) C
  proj₁ = record
      { fobj = ∧-eliml
      ; fmap = ∧-eliml
      ; fmap-resp = ∧-eliml
      ; fmap-id = C.≈.refl
      ; fmap-∘ = λ _ _ → C.≈.refl
      }


  proj₂ : Functor (C × D) D
  proj₂ = record
      { fobj = ∧-elimr
      ; fmap = ∧-elimr
      ; fmap-resp = ∧-elimr
      ; fmap-id = D.≈.refl
      ; fmap-∘ = λ _ _ → D.≈.refl
      }
