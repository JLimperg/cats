{-# OPTIONS --without-K --safe #-}
module Cats.Profunctor where

open import Data.Product using (_,_)
open import Level using (suc ; _⊔_)

open import Cats.Category
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Category.Setoids using (Setoids)
open import Cats.Functor

import Cats.Category.Cat as Cat
import Cats.Category.Cat.Facts.Product as Cat


-- The usual definition inverts C and D, so
--
--   Profunctor C D E = Functor (Dᵒᵖ × C) E
--
-- but that's just confusing.
Profunctor : ∀ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  → Category lo la l≈
  → Category lo′ la′ l≈′
  → Category lo″ la″ l≈″
  → Set (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′ ⊔ lo″ ⊔ la″ ⊔ l≈″)
Profunctor C D E = Functor ((C ᵒᵖ) × D) E


module Profunctor {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  {C : Category lo la l≈}
  {D : Category lo′ la′ l≈′}
  {E : Category lo″ la″ l≈″}
  (F : Profunctor C D E)
  where

  private
    module C = Category C
    module D = Category D
    module E = Category E


  pobj : C.Obj → D.Obj → E.Obj
  pobj c d = fobj F (c , d)


  pmap : ∀ {c c′} (f : c′ C.⇒ c) {d d′} (g : d D.⇒ d′)
    → pobj c d E.⇒ pobj c′ d′
  pmap f g = fmap F (f , g)


  pmap₁ : ∀ {c c′ d} (f : c′ C.⇒ c)
    → pobj c d E.⇒ pobj c′ d
  pmap₁ f = pmap f D.id


  pmap₂ : ∀ {c d d′} (g : d D.⇒ d′)
    → pobj c d E.⇒ pobj c d′
  pmap₂ g = pmap C.id g


open Profunctor public


Functor→Profunctor₁ : ∀ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  → {C : Category lo la l≈} {D : Category lo′ la′ l≈′} {X : Category lo″ la″ l≈″}
  → Functor (C ᵒᵖ) D
  → Profunctor C X D
Functor→Profunctor₁ F = F Cat.∘ Cat.projl


Functor→Profunctor₂ : ∀ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  → {C : Category lo la l≈} {D : Category lo′ la′ l≈′} {X : Category lo″ la″ l≈″}
  → Functor C D
  → Profunctor X C D
Functor→Profunctor₂ F = F Cat.∘ Cat.projr
