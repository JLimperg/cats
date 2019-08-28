{-# OPTIONS --without-K --safe #-}
module Cats.Category.Presheaves.Facts.Exponential where

open import Data.Product using (_,_)
open import Relation.Binary using (Setoid)

open import Cats.Category
open import Cats.Category.Fun using (Fun ; ≈-intro ; ≈-elim)
open import Cats.Category.Presheaves using (Presheaves)
open import Cats.Category.Setoids as Setoids using (≈-intro ; ≈-elim)
open import Cats.Functor using (Functor)
open import Cats.Trans using (Trans ; component ; natural)

import Cats.Category.Fun.Facts.Product as Product
import Cats.Category.Setoids.Facts

open Functor
open HasBinaryProducts {{...}}
open Setoids._⇒_


module _ {l} {ℂ : Category l l l} where

  private
    module ℂ = Category ℂ
    open Category (Presheaves ℂ l l)
    module $ (F : Obj) {x : Category.Obj ℂ} = Setoid (fobj F x)


  -- Could replace this with transposeBifunctor₂ HomF, but that would introduce
  -- even more redundant compositions with the identity.
  y : ℂ.Obj → Obj
  y d = record
    { fobj = λ c → ℂ.Hom c d
    ; fmap = λ f → record
      { arr = (ℂ._∘ f)
      ; resp = ℂ.∘-resp-l
      }
    ; fmap-resp = λ eq₁ → ≈-intro λ eq₂ → ℂ.∘-resp eq₂ eq₁
    ; fmap-id = ≈-intro λ eq → ℂ.≈.trans ℂ.id-r eq
    ; fmap-∘ = ≈-intro λ eq → ℂ.≈.trans ℂ.assoc (ℂ.∘-resp-l eq)
    }


  _↝_ : (F G : Obj) → Obj
  F ↝ G = record
    { fobj = λ d → Hom (y d × F) G
    ; fmap = λ {d} {d′} f → record
      { arr = λ α → record
        { component = λ d → record
          { arr = λ where
              (g , c) → arr (component α d) (f ℂ.∘ g , c)
          ; resp = λ where
              (eq₁ , eq₂) → resp (component α d) (ℂ.∘-resp-r eq₁ , eq₂)
          }
        ; natural = λ {e} {e′} {g} → ≈-intro λ where
            {h , c} {h′ , c′} (h≈h′ , c≈c′) →
              $.trans G (resp (component α e′) (ℂ.unassoc , $.refl F))
                (≈-elim (natural α) (ℂ.∘-resp-r h≈h′ , c≈c′))
        }
      ; resp = λ α≈β → ≈-intro (≈-intro λ where
          (f≈g , h≈i) → ≈-elim (≈-elim α≈β) (ℂ.∘-resp-r f≈g , h≈i))
      }
    ; fmap-resp = λ f≈g → ≈-intro λ α≈β → ≈-intro (≈-intro λ where
        (c≈d , h≈i) → ≈-elim (≈-elim α≈β) ((ℂ.∘-resp f≈g c≈d) , h≈i))
    ; fmap-id = ≈-intro λ α≈β → ≈-intro (≈-intro λ where
        (c≈d , h≈i) → ≈-elim (≈-elim α≈β) ((ℂ.≈.trans ℂ.id-l c≈d) , h≈i))
    ; fmap-∘ = ≈-intro λ α≈β → ≈-intro (≈-intro λ where
        (c≈d , h≈i) → ≈-elim (≈-elim α≈β) ((ℂ.≈.trans ℂ.unassoc (ℂ.∘-resp-r c≈d)) , h≈i))
    }


  Eval : ∀ F G → F ↝ G × F ⇒ G
  Eval F G = record
    { component = λ c → record
      { arr = λ where
          (α , x) → arr (component α c) (ℂ.id , x)
      ; resp = λ where
          (α≈β , f≈g) → ≈-elim (≈-elim α≈β) (ℂ.≈.refl , f≈g)
      }
    ; natural = λ {c} {d} → ≈-intro λ where
        {α , f} {β , g} (α≈β , f≈g) →
          $.trans G
            (≈-elim (≈-elim α≈β)
              (ℂ.≈.trans ℂ.id-r (ℂ.≈.sym ℂ.id-l) , resp (fmap F _) f≈g))
            (≈-elim (natural β) (ℂ.≈.refl , $.refl F))
    }


  Curry : ∀ E F G → E × F ⇒ G → E ⇒ F ↝ G
  Curry E F G α = record
    { component = λ d → record
      { arr = λ x → record
        { component = λ c → record
          { arr = λ where
              (f , y) → arr (component α c) (arr (fmap E f) x , y)
          ; resp = λ where
              (c≈d , x≈y) → resp (component α c)
                (≈-elim (fmap-resp E c≈d) ($.refl E) , x≈y)
          }
        ; natural = ≈-intro λ where
            (f≈g , x≈y) → $.trans G
              (resp (component α _)
                (($.sym E (≈-elim (fmap-∘ E) ($.refl E))) , ($.refl F)))
              (≈-elim (natural α) (≈-elim (fmap-resp E f≈g) ($.refl E) , x≈y))
        }
      ; resp = λ x≈y → ≈-intro (≈-intro λ where
          (f≈g , c≈d) → resp (component α _) ((≈-elim (fmap-resp E f≈g) x≈y) , c≈d))
      }
    ; natural = ≈-intro λ x≈y → ≈-intro (≈-intro λ where
        (f≈g , c≈d) → resp (component α _)
          ( $.trans E (≈-elim (fmap-∘ E) x≈y)
              (≈-elim (fmap-resp E (ℂ.∘-resp-r f≈g)) ($.refl E))
          , c≈d ))
    }


  instance
    hasExponentials : HasExponentials (Presheaves ℂ l l)
    hasExponentials = record
      { hasBinaryProducts = Product.hasBinaryProducts
      ; _↝′_ = λ F G → record
        { Cᴮ = F ↝ G
        ; eval = Eval F G
        ; curry′ = λ {E} α → record
          { arr = Curry E F G α
          ; prop = ≈-intro (≈-intro λ where
              (x≈y , u≈v) → resp (component α _) (≈-elim (fmap-id E) x≈y , u≈v))
          ; unique = λ {α} α≈ → ≈-intro (≈-intro (λ x≈y → ≈-intro (≈-intro (λ where
              (f≈g , u≈v) → $.trans G
                (≈-elim (≈-elim (≈.sym α≈)) (≈-elim (fmap-resp E f≈g) ($.refl E) , u≈v))
                ($.trans G
                  (≈-elim (≈-elim (≈-elim (natural α) x≈y)) (ℂ.≈.refl , ($.refl F)))
                  (resp (component (arr (component α _) _) _) (ℂ.id-r , ($.refl F))))))))
          }
        }
      }
