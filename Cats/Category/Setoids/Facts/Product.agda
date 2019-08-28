{-# OPTIONS --without-K --safe #-}
module Cats.Category.Setoids.Facts.Product where

open import Data.Product as P using (_,_ ; <_,_>)
open import Data.Product.Relation.Pointwise.NonDependent using (×-setoid)
open import Relation.Binary using (Setoid)

open import Cats.Category
open import Cats.Category.Setoids as Setoids using (Setoids ; ≈-intro ; ≈-elim)
open import Cats.Util.Conv

import Cats.Category.Setoids.Facts.Terminal

open Setoid using (Carrier ; refl ; sym ; trans) renaming (_≈_ to _≣_)


-- The existence of binary products, proven below, already follows from the
-- existence of general products, proven further below. We still construct them
-- explicitly because the definitions in this module are much easier to work
-- with.
module BuildBinary l l≈ where

  infixr 2 _×_


  open Category (Setoids l l≈)
  open Setoids._⇒_ using (resp)


  _×_ : Obj → Obj → Obj
  _×_ = ×-setoid


  projl : ∀ {A B} → A × B ⇒ A
  projl {A} {B} = record
      { arr = P.proj₁
      ; resp = λ { (eq₁ , eq₂) → eq₁ }
      }


  projr : ∀ {A B} → A × B ⇒ B
  projr {A} {B} = record
      { arr = P.proj₂
      ; resp = λ { (eq₁ , eq₂) → eq₂ }
      }


  ⟨_,_⟩ : ∀ {X A B} → X ⇒ A → X ⇒ B → X ⇒ A × B
  ⟨_,_⟩ {A = A} {B} xl xr = record
      { arr = < xl ⃗ , xr ⃗ >
      ; resp = λ eq → resp xl eq , resp xr eq
      }


  isBinaryProduct : ∀ {A B} → IsBinaryProduct (A × B) projl projr
  isBinaryProduct xl xr = record
    { arr = ⟨ xl , xr ⟩
    ; prop = (≈-intro λ eq → resp xl eq) , (≈-intro λ eq → resp xr eq)
    ; unique = λ { (eq₁ , eq₂) → ≈-intro λ x≈y → ≈-elim eq₁ x≈y , ≈-elim eq₂ x≈y }
    }


  _×′_ : ∀ A B → BinaryProduct A B
  A ×′ B = mkBinaryProduct projl projr isBinaryProduct


instance
  hasBinaryProducts : ∀ {l l≈} → HasBinaryProducts (Setoids l l≈)
  hasBinaryProducts {l} {l≈} .HasBinaryProducts._×′_ = BuildBinary._×′_ l l≈


module Build l {I : Set l} where

  open Category (Setoids l l)
  open Setoids._⇒_ using (resp)


  Π : (O : I → Obj) → Obj
  Π O = record
      { Carrier = ∀ i → Carrier (O i)
      ; _≈_ = λ f g → ∀ i → _≣_ (O i) (f i) (g i)
      ; isEquivalence = record
          { refl = λ i → refl (O i)
          ; sym = λ eq i → sym (O i) (eq i)
          ; trans = λ eq₁ eq₂ i → trans (O i) (eq₁ i) (eq₂ i)
          }
      }


  proj : ∀ {O : I → Obj} i → Π O ⇒ O i
  proj i = record
      { arr = λ f → f i
      ; resp = λ eq → eq i
      }


  isProduct : ∀ {O : I → Obj} → IsProduct O (Π O) proj
  isProduct x = record
      { arr = record
          { arr = λ a i → (x i ⃗) a
          ; resp = λ eq i → resp (x i) eq
          }
      ; prop = λ i → ≈-intro λ eq → resp (x i) eq
      ; unique = λ x-candidate → ≈-intro λ eq i → ≈-elim (x-candidate i) eq
      }


  Π′ : (O : I → Obj) → Product O
  Π′ O = record { prod = Π O ; proj = proj ; isProduct = isProduct }


instance
  hasProducts : ∀ {l} → HasProducts l (Setoids l l)
  hasProducts {l} = record { Π′ = Build.Π′ l }

  hasFiniteProducts : ∀ {l l≈} → HasFiniteProducts (Setoids l l≈)
  hasFiniteProducts = record {}
