module Cats.Category.Preorder where

open import Data.Unit using (⊤ ; tt)
open import Level
open import Relation.Binary as Rel
  using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)

open import Cats.Category
open import Cats.Util.Function as Fun using (_on_)


module _ lc l≈ l≤ where

  infixr 9 _∘_
  infixr 4 _≈_


  Obj : Set (suc (lc ⊔ l≈ ⊔ l≤))
  Obj = Rel.Preorder lc l≈ l≤


  record _⇒_ (A B : Obj) : Set (lc ⊔ l≈ ⊔ l≤) where
    private
      module A = Rel.Preorder A
      module B = Rel.Preorder B

    field
      arr : A.Carrier → B.Carrier
      resp : ∀ {x y} → x A.≈ y → arr x B.≈ arr y
      monotone : ∀ {x y} → x A.∼ y → arr x B.∼ arr y

  open _⇒_


  id : ∀ {A} → A ⇒ A
  id = record { arr = Fun.id ; resp = λ eq → eq ; monotone = λ eq → eq }


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  g ∘ f = record
      { arr = arr g Fun.∘ arr f
      ; monotone = monotone g Fun.∘ monotone f
      ; resp = resp g Fun.∘ resp f
      }


  -- TODO Generalise extensional function equality so that we can use it here.
  -- The reason we can't right now is that extensional function equality assumes
  -- x ≡ y instead of x A.≈ y.
  _≈_ : {A B : Obj} → Rel (A ⇒ B) (lc ⊔ l≈)
  _≈_ {A} {B} f g = ∀ {x y} → x A.≈ y → arr f x B.≈ arr g y
    where
      module A = Rel.Preorder A
      module B = Rel.Preorder B


  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv {A} {B} = record
     { refl = λ {f} x≈y → resp f x≈y
     ; sym = λ f≈g x≈y → B.Eq.sym (f≈g (A.Eq.sym x≈y))
     ; trans = λ f≈g g≈h x≈y → B.Eq.trans (f≈g x≈y) (g≈h A.Eq.refl)
     }
   where
     module A = Rel.Preorder A
     module B = Rel.Preorder B


  ∘-resp : ∀ {A B C} → (_∘_ {A} {B} {C}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ∘-resp {A} {B} {C} {f} {g} {h} {i} f≈g h≈i x≈y
      = C.Eq.trans (f≈g (h≈i x≈y)) (resp g B.Eq.refl)
    where
      module B = Rel.Preorder B
      module C = Rel.Preorder C


  instance Preorder : Category (suc (lc ⊔ l≈ ⊔ l≤)) (lc ⊔ l≈ ⊔ l≤) (lc ⊔ l≈)
  Preorder = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = λ {_} {_} {_} {f} {g} {h} {i} → ∘-resp {x = f} {g} {h} {i}
      ; id-r = λ {_} {_} {f} → resp f
      ; id-l = λ {_} {_} {f} → resp f
      ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → resp (f ∘ g ∘ h)
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
