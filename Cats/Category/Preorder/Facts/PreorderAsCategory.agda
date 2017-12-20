module Cats.Category.Preorder.Facts.PreorderAsCategory where

open import Relation.Binary using (Preorder)

import Level

open import Cats.Category
open import Cats.Category.Preorder using (preorderAsCategory)
open import Cats.Util.Logic.Constructive


module _ {lc l≈ l≤} (P : Preorder lc l≈ l≤) where

  C : Category _ _ _
  C = preorderAsCategory P


  open module P = Preorder P using (_∼_) renaming (_≈_ to _≋_)
  open Category C


  _≈_⊔_ : Obj → Obj → Obj → Set l≤
  lub ≈ x ⊔ y = x ∼ lub ∧ y ∼ lub ∧ (lub ∼ x ∨ lub ∼ y)


  _≈_⊓_ : Obj → Obj → Obj → Set l≤
  glb ≈ x ⊓ y = glb ∼ x ∧ glb ∼ y ∧ (x ∼ glb ∨ y ∼ glb)


  IsMinimum : Obj → Set (lc Level.⊔ l≤)
  IsMinimum m = ∀ x → m ∼ x


  IsMaximum : Obj → Set (lc Level.⊔ l≤)
  IsMaximum m = ∀ x → x ∼ m


  initial : ∀ {x} → IsMinimum x → IsInitial x
  initial min y = (min y) , _


  terminal : ∀ {x} → IsMaximum x → IsTerminal x
  terminal max y = (max y) , _


  ⊓-isBinaryProduct : ∀ {glb x y}
    → (pl : glb ∼ x)
    → (pr : glb ∼ y)
    → (x ∼ glb ∨ y ∼ glb)
    → IsBinaryProduct glb pl pr
  ⊓-isBinaryProduct pl pr (∨-introl x∼glb) xl xr = ∃!-intro (x∼glb ∘ xl) _  _
  ⊓-isBinaryProduct pl pr (∨-intror y∼glb) xl xr = ∃!-intro (y∼glb ∘ xr) _ _


  ⊓-to-BinaryProduct : ∀ {glb x y} → glb ≈ x ⊓ y → BinaryProduct x y
  ⊓-to-BinaryProduct {glb} (pl , pr , maximal) = record
    { prod = glb
    ; projl = pl
    ; projr = pr
    ; isBinaryProduct = ⊓-isBinaryProduct pl pr maximal
    }


  mono : ∀ {x y} (f : x ⇒ y) → IsMono f
  mono = _


  epi : ∀ {x y} (f : x ⇒ y) → IsEpi f
  epi = _


  unique : ∀ {x y} (f : x ⇒ y) → IsUnique f
  unique = _
