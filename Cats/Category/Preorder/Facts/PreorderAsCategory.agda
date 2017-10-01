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


  product : ∀ {glb x y} → (glb ≈ x ⊓ y) → x × y
  product {glb} {x} {y} (glb∼x , glb∼y , ∨-introl x∼glb) = record
      { prod = glb
      ; projl = glb∼x
      ; projr = glb∼y
      ; ump = λ {z} z∼x z∼y → P.trans z∼x x∼glb , _
      }
  product {glb} {x} {y} (glb∼x , glb∼y , ∨-intror y∼glb) = record
      { prod = glb
      ; projl = glb∼x
      ; projr = glb∼y
      ; ump = λ {z} z∼x z∼y → P.trans z∼y y∼glb , _
      }


  mono : ∀ {x y} (f : x ⇒ y) → IsMono f
  mono = _


  epi : ∀ {x y} (f : x ⇒ y) → IsEpi f
  epi = _


  unique : ∀ {x y} (f : x ⇒ y) → IsUnique f
  unique = _
