module Cats.Category.Sigma where

open import Data.Product using (Σ-syntax ; _,_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel ; IsEquivalence)

open import Cats.Category
open import Cats.Category.Cat using (Cat)
open import Cats.Functor using (Functor)
open import Cats.Trans using (Trans)
open import Cats.Trans.Iso using (NatIso)

open Functor
open Trans

private
  module ℂ = Category


module Build {lo la l≈ lo′ la′ l≈′} {C : Category lo la l≈}
  (F : Functor C (Cat lo′ la′ l≈′))
  (let module C = Category C)
  (let module F = Functor F)
  -- Here are some of the coherence conditions we need.
  (F-fmap-resp-refl-forth : ∀ {a b} {f : a C.⇒ b} {c}
    → let module Fb = Category (F.fobj b) in
      NatIso.Forth (F.fmap-resp {i = f} C.≈.refl) .component c Fb.≈ Fb.id)
  (F-fmap-resp-sym-forth : ∀ {a b} {f g : a C.⇒ b} {f≈g : f C.≈ g} {c}
    → let module Fb = Category (F.fobj b) in
      NatIso.Forth (F.fmap-resp (C.≈.sym f≈g)) .component c Fb.≈
      NatIso.Back (F.fmap-resp f≈g) .component c)
  (F-fmap-resp-trans-forth : ∀ {a b} {f g h : a C.⇒ b} {f≈g : f C.≈ g} {g≈h : g C.≈ h} {c}
    → let module Fb = Category (F.fobj b) in
      NatIso.Forth (F.fmap-resp (C.≈.trans f≈g g≈h)) .component c Fb.≈
      NatIso.Forth (F.fmap-resp g≈h) .component c Fb.∘ NatIso.Forth (F.fmap-resp f≈g) .component c)
  where

  infixr -1  _⇒_
  infix  4   _≈_
  infixr 9   _∘_


  -- Should be a consequence of F-fmap-resp-refl-forth.
  F-fmap-resp-refl-back : ∀ {a b} {f : a C.⇒ b} {c}
    → let module Fb = Category (F.fobj b) in
      NatIso.Back (F.fmap-resp {i = f} C.≈.refl) .component c Fb.≈ Fb.id
  F-fmap-resp-refl-back {a} {b} {f} {c} = {!!}
    where
      module Fb = Category (F.fobj b)


  Obj : Set (lo ⊔ lo′)
  Obj = Σ[ a ∈ C.Obj ] F.fobj a .ℂ.Obj


  _⇒_ : (a b : Obj) → Set (la ⊔ la′)
  (a , a⁺) ⇒ (b , b⁺) = Σ[ f ∈ a C.⇒ b ] ℂ.Hom′ (F.fobj b) (F.fmap f .fobj a⁺) b⁺


  _≈_ : ∀ {a b} → Rel (a ⇒ b) (l≈ ⊔ l≈′)
  _≈_ {a , a⁺} {b , b⁺} (f , f⁺) (g , g⁺)
    = Σ[ f≈g ∈ f C.≈ g ]
      f⁺ Fb.∘ NatIso.Back (F.fmap-resp f≈g) .component a⁺ Fb.≈ g⁺
    where
      module Fb = Category (F.fobj b)


  equiv : ∀ {a b} → IsEquivalence (_≈_ {a} {b})
  equiv {a , a⁺} {b , b⁺} = record
    { refl = λ { {f , f⁺} → C.≈.refl , Fb.≈.trans (Fb.∘-resp-r F-fmap-resp-refl-back) Fb.id-r }
    ; sym = λ { {f , f⁺} {g , g⁺} (f≈g , f⁺≈g⁺) → C.≈.sym f≈g , {!!} }
    ; trans = {!!}
    }
    where
      module Fb = Category (F.fobj b)


  id : ∀ {a} → a ⇒ a
  id {a , a⁺} = C.id , NatIso.Forth F.fmap-id .component a⁺


  _∘_ : ∀ {a b c} → b ⇒ c → a ⇒ b → a ⇒ c
  _∘_ {a , a⁺} {b , b⁺} {c , c⁺} (f , f⁺) (g , g⁺)
    = f C.∘ g
    , f⁺ Fc.∘ Ff.fmap g⁺ Fc.∘ NatIso.Back (F.fmap-∘ {f = f} {g}) .component a⁺
    where
      module Fc = Category (F.fobj c)
      module Ff = Functor (F.fmap f)


  id-l : ∀ {a b} {f : a ⇒ b} → id ∘ f ≈ f
  id-l {a , a⁺} {b , b⁺} {f , f⁺} = C.id-l , {!!}
    where
      module Fb = Category (F.fobj b)
