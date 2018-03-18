module Cats.Category.Cat.Facts.Product where

open import Data.Bool using (true ; false)
open import Data.Product using (_,_)

open import Cats.Category
open import Cats.Category.Cat using (Cat)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Category.Product.Binary.Facts using (proj₁ ; proj₂ ; iso-intro)
open import Cats.Functor using (Functor)
open import Cats.Util.Logic.Constructive using (_∧_)


module _ {lo la l≈} where

  open module Cat = Category (Cat lo la l≈) using
    (IsBinaryProduct ; ∃!-intro ; IsUniqueSuchThat ; mkBinaryProduct)


  isBinaryProduct : ∀ {C D : Category lo la l≈}
    → IsBinaryProduct (C × D) proj₁ proj₂
  isBinaryProduct {C} {D} {X} xl xr = ∃!-intro arr (prop₁ , prop₂) unique
    where
      module C = Category C
      module D = Category D
      module xl = Functor xl
      module xr = Functor xr

      arr : Functor X (C × D)
      arr = record
          { fobj = λ x → xl.fobj x , xr.fobj x
          ; fmap = λ f → xl.fmap f , xr.fmap f
          ; fmap-resp = λ eq → xl.fmap-resp eq , xr.fmap-resp eq
          ; fmap-id = xl.fmap-id , xr.fmap-id
          ; fmap-∘ = λ f g → xl.fmap-∘ f g , xr.fmap-∘ f g
          }

      prop₁ : xl Cat.≈ proj₁ Cat.∘ arr
      prop₁ = record
          { iso = C.≅.refl
          ; fmap-≈ = λ _ → C.≈.sym (C.≈.trans C.id-l C.id-r)
          }

      prop₂ : xr Cat.≈ proj₂ Cat.∘ arr
      prop₂ = record
          { iso = D.≅.refl
          ; fmap-≈ = λ _ → D.≈.sym (D.≈.trans D.id-l D.id-r)
          }

      unique :
        IsUniqueSuchThat (λ u → xl Cat.≈ proj₁ Cat.∘ u ∧ xr Cat.≈ proj₂ Cat.∘ u) arr
      unique {F} (eql , eqr) = record
          { iso = iso-intro (iso eql) (iso eqr)
          ; fmap-≈ = λ f → fmap-≈ eql f , fmap-≈ eqr f
          }
        where
          open Cats.Category.Cat.Build._≈_


  instance
    hasBinaryProducts : HasBinaryProducts (Cat lo la l≈)
    hasBinaryProducts .HasBinaryProducts._×′_ C D
        = mkBinaryProduct proj₁ proj₂ isBinaryProduct
