module Cats.Category.Setoids.Facts.Products where

open import Data.Product as P using (_,_ ; <_,_>)
open import Relation.Binary.Product.Pointwise using (_×-setoid_)

open import Cats.Category
open import Cats.Category.Setoids as Setoids using (Setoids)
open import Cats.Util.Conv


-- TODO Generalise to infinite products.

module Build l l≈ where

  infixr 2 _×_


  open Category (Setoids l l≈)
  open Setoids.Build._⇒_ using (resp)


  _×_ : Obj → Obj → Obj
  _×_ = _×-setoid_


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
    ; prop = (λ eq → resp xl eq) , (λ eq → resp xr eq)
    ; unique = λ { (eq₁ , eq₂) x≈y → eq₁ x≈y , eq₂ x≈y }
    }


  _×′_ : ∀ A B → BinaryProduct A B
  A ×′ B = mkBinaryProduct projl projr isBinaryProduct


instance hasBinaryProducts : ∀ l l≈ → HasBinaryProducts (Setoids l l≈)
hasBinaryProducts l l≈ .HasBinaryProducts._×′_ = Build._×′_ l l≈
