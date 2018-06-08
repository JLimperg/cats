module Cats.Adjunction where

open import Level using (suc ; _⊔_)

open import Cats.Category
open import Cats.Category.Cat.Facts.Product using (First ; Second)
open import Cats.Category.Fun using (Fun)
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Category.Setoids using (Setoids)
open import Cats.Functor using (Functor ; _∘_)
open import Cats.Functor.Op using (Op)
open import Cats.Functor.Representable using (Hom[_])

open Functor


module _ {lo la l≈} {C D : Category lo la l≈} where

  private
    module Fun = Category (Fun ((C ᵒᵖ) × D) (Setoids la l≈))


  record Adjunction (F : Functor C D) (U : Functor D C)
    : Set (lo ⊔ suc la ⊔ suc l≈)
    where
    field
      iso : (Hom[ D ] ∘ First (Op F)) Fun.≅ (Hom[ C ] ∘ Second U)
