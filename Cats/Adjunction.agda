module Cats.Adjunction where

open import Data.Product using (_,_)
open import Level using (suc ; _⊔_)

open import Cats.Category
open import Cats.Category.Cat using (Cat)
open import Cats.Category.Cat.Facts.Product using (hasBinaryProducts)
open import Cats.Category.Constructions.Product using (HasBinaryProducts)
open import Cats.Category.Fun using (Fun)
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Category.Setoids using (Setoids)
open import Cats.Functor using (Functor ; _∘_)
open import Cats.Functor.Op using (Op)
open import Cats.Functor.Representable using (Hom[_])

open Functor


-- We force C and D to be at the same levels. This could probably be relaxed if
-- needed.
module _ {lo la l≈} {C D : Category lo la l≈} where

  private
    open module HBP {lo} {la} {l≈} =
      HasBinaryProducts (hasBinaryProducts {lo} {la} {l≈})
    module Fun = Category (Fun ((C ᵒᵖ) × D) (Setoids la l≈))


  record Adjunction (F : Functor C D) (U : Functor D C)
    : Set (lo ⊔ suc la ⊔ suc l≈)
    where
    field
      iso : (Hom[ D ] ∘ first (Op F)) Fun.≅ (Hom[ C ] ∘ second U)
