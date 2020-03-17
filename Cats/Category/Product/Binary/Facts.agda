{-# OPTIONS --without-K --safe #-}
module Cats.Category.Product.Binary.Facts where

open import Data.Product using (_,_ ; proj₁ ; proj₂) renaming (_×_ to _×T_)

open import Cats.Category
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Functor


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


  iso-elim : ∀ {A A′ B B′} → (A , B) ×.≅ (A′ , B′) → A C.≅ A′ ×T B D.≅ B′
  iso-elim f
      = record
      { forth = proj₁ (forth f)
      ; back = proj₁ (back f)
      ; back-forth = proj₁ (back-forth f)
      ; forth-back = proj₁ (forth-back f)
      }
      , record
      { forth = proj₂ (forth f)
      ; back = proj₂ (back f)
      ; back-forth = proj₂ (back-forth f)
      ; forth-back = proj₂ (forth-back f)
      }
