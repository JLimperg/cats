module Cats.Category.Setoids.Facts.Products where

open import Data.Product as P using (_,_ ; <_,_>)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Product.Pointwise using (_×-setoid_)

open import Cats.Category
open import Cats.Category.Setoids as Setoids using (Setoids)
open import Cats.Util.Conv

open Setoid using (Carrier ; refl ; sym ; trans) renaming (_≈_ to _≣_)


-- The existence of binary products, proven below, already follows from the
-- existence of general products, proven further below. We still construct them
-- explicitly because the definitions in this module are much easier to work
-- with.
module BuildBinary l l≈ where

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


instance
  hasBinaryProducts : ∀ l l≈ → HasBinaryProducts (Setoids l l≈)
  hasBinaryProducts l l≈ .HasBinaryProducts._×′_ = BuildBinary._×′_ l l≈


module Build l {I : Set l} where

  open Category (Setoids l l)
  open Setoids.Build._⇒_ using (resp)


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
      ; prop = λ i eq → resp (x i) eq
      ; unique = λ x-candidate eq i → x-candidate i eq
      }


  Π′ : (O : I → Obj) → Product O
  Π′ O = record { prod = Π O ; proj = proj ; isProduct = isProduct }


instance
  hasProducts : ∀ l → HasProducts l (Setoids l l)
  hasProducts l = record { Π′ = Build.Π′ l }
