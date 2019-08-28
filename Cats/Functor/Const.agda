{-# OPTIONS --without-K --safe #-}
module Cats.Functor.Const where

open import Function using (const)

open import Cats.Category
open import Cats.Functor using (Functor)


module _ {lo la l≈ lo′ la′ l≈′}
  (C : Category lo la l≈) {D : Category lo′ la′ l≈′}
  where

  open Category D


  Const : Obj → Functor C D
  Const d = record
    { fobj = const d
    ; fmap = const id
    ; fmap-resp = const ≈.refl
    ; fmap-id = ≈.refl
    ; fmap-∘ = id-l
    }
