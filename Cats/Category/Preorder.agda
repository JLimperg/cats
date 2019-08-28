{-# OPTIONS --without-K --safe #-}
module Cats.Category.Preorder where

open import Data.Unit using (⊤ ; tt)
open import Level
open import Relation.Binary as Rel
  using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_ ; Setoid)

open import Cats.Category
open import Cats.Category.Setoids using (Setoids ; ≈-intro)
open import Cats.Util.Conv
open import Cats.Util.Function as Fun using (_on_)


module _ {lc l≈ l≤ : Level} where

  infixr 9 _∘_
  infixr 4 _≈_


  private
    module Setoids = Category (Setoids lc l≈)


  Obj : Set (suc (lc ⊔ l≈ ⊔ l≤))
  Obj = Rel.Preorder lc l≈ l≤


  Universe : Obj → Setoid lc l≈
  Universe A = record
      { Carrier = Rel.Preorder.Carrier A
      ; _≈_ = Rel.Preorder._≈_ A
      ; isEquivalence = Rel.Preorder.isEquivalence A
      }


  record _⇒_ (A B : Obj) : Set (lc ⊔ l≈ ⊔ l≤) where
    private
      module A = Rel.Preorder A
      module B = Rel.Preorder B

    field
      arr : Universe A Setoids.⇒ Universe B
      monotone : ∀ {x y} → x A.∼ y → (arr ⃗) x B.∼ (arr ⃗) y

    open Cats.Category.Setoids._⇒_ arr public using (resp)

  open _⇒_ using (monotone ; resp)


  instance
    HasArrow-⇒ : ∀ {A B} → HasArrow (A ⇒ B) _ _ _
    HasArrow-⇒ = record { Cat = Setoids lc l≈ ; _⃗ = _⇒_.arr }


  id : ∀ {A} → A ⇒ A
  id = record { arr = Setoids.id ; monotone = Fun.id }


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  g ∘ f = record
      { arr = g ⃗ Setoids.∘ f ⃗
      ; monotone = monotone g Fun.∘ monotone f
      }


  _≈_ : {A B : Obj} → Rel (A ⇒ B) (lc ⊔ l≈)
  _≈_ = Setoids._≈_ on _⃗


  Preorder : Category (suc (lc ⊔ l≈ ⊔ l≤)) (lc ⊔ l≈ ⊔ l≤) (lc ⊔ l≈)
  Preorder = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = Fun.on-isEquivalence _⃗ Setoids.equiv
      ; ∘-resp = Setoids.∘-resp
      ; id-r = Setoids.id-r
      ; id-l = Setoids.id-l
      ; assoc = λ { {f = f} {g} {h} → Setoids.assoc {f = f ⃗} {g ⃗} {h ⃗} }
      }


preorderAsCategory : ∀ {lc l≈ l≤} → Rel.Preorder lc l≈ l≤ → Category lc l≤ zero
preorderAsCategory P = record
    { Obj = P.Carrier
    ; _⇒_ = P._∼_
    ; _≈_ = λ _ _ → ⊤
    ; id = P.refl
    ; _∘_ = λ B≤C A≤B → P.trans A≤B B≤C
    ; equiv = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    ; ∘-resp = λ _ _ → tt
    ; id-r = tt
    ; id-l = tt
    ; assoc = tt
    }
  where
    module P = Rel.Preorder P
