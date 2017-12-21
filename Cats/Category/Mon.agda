module Cats.Category.Mon where

open import Data.Unit using (⊤)
open import Relation.Binary using (Setoid ; _Preserves₂_⟶_⟶_ ; IsEquivalence)
open import Level using (Level ; zero ; suc ; _⊔_)

open import Cats.Category
import Cats.Util.Function as Fun


record Monoid l l≈ : Set (suc (l ⊔ l≈)) where
  infixr 9 _⊕_

  field
    Universe : Setoid l l≈

  open Setoid Universe public

  field
    _⊕_ : Carrier → Carrier → Carrier
    unit : Carrier

    ⊕-resp : _⊕_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    assoc : ∀ {a b c} → (a ⊕ b) ⊕ c ≈ a ⊕ (b ⊕ c)
    id-l : ∀ {a} → unit ⊕ a ≈ a
    id-r : ∀ {a} → a ⊕ unit ≈ a

  module ≈ = IsEquivalence isEquivalence


module _ (l l≈ : Level) where

  infixr 9 _∘_
  infixr 4 _≈_


  Obj : Set (suc (l ⊔ l≈))
  Obj = Monoid l l≈


  record _⇒_ (M N : Obj) : Set (l ⊔ l≈) where
    private
      module M = Monoid M
      module N = Monoid N

    field
      arr : M.Carrier → N.Carrier
      resp : ∀ {x y} → x M.≈ y → arr x N.≈ arr y
      unit : arr M.unit N.≈ N.unit
      lift : ∀ {n m} → arr (n M.⊕ m) N.≈ arr n N.⊕ arr m

  open _⇒_


  id : ∀ {M} → M ⇒ M
  id {M} = record
      { arr = Fun.id
      ; resp = Fun.id
      ; unit = M.≈.refl
      ; lift = M.≈.refl
      }
    where
      module M = Monoid M


  _≈_ : ∀ {M N} (f g : M ⇒ N) → Set (l≈ ⊔ l)
  _≈_ {M} {N} f g = ∀ {x y} → x M.≈ y → arr f x N.≈ arr g y
    where
      module M = Monoid M
      module N = Monoid N


  equiv : ∀ {M N} → IsEquivalence (_≈_ {M} {N})
  equiv {M} {N} = record
      { refl = λ {f} → resp f
      ; sym = λ f≈g x≈y → N.≈.sym (f≈g (M.≈.sym x≈y))
      ; trans = λ f≈g g≈h x≈y → N.≈.trans (f≈g x≈y) (g≈h M.≈.refl)
      }
    where
      module M = Monoid M
      module N = Monoid N


  _∘_ : ∀ {M N O} → (N ⇒ O) → (M ⇒ N) → (M ⇒ O)
  _∘_ {M} {N} {O} f g = record
      { arr = arr f Fun.∘ arr g
      ; resp = resp f Fun.∘ resp g
      ; unit = O.≈.trans (resp f (unit g)) (unit f)
      ; lift = O.≈.trans (resp f (lift g)) (lift f)
      }
    where
      module O = Monoid O


  Mon : Category (suc (l≈ ⊔ l)) (l≈ ⊔ l) (l≈ ⊔ l)
  Mon = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = λ f≈g h≈i → f≈g Fun.∘ h≈i
      ; id-r = λ {M} {N} {f} → resp f
      ; id-l = λ {M} {N} {f} → resp f
      ; assoc = λ {_} {_} {_} {_} {f} {g} {h} x≈y → resp f (resp g (resp h x≈y))
      }


monoidAsCategory : ∀ {l l≈} → Monoid l l≈ → Category zero l l≈
monoidAsCategory M = record
    { Obj = ⊤
    ; _⇒_ = λ _ _ → M.Carrier
    ; _≈_ = M._≈_
    ; id = M.unit
    ; _∘_ = M._⊕_
    ; equiv = M.isEquivalence
    ; ∘-resp = M.⊕-resp
    ; id-r = M.id-r
    ; id-l = M.id-l
    ; assoc = M.assoc
    }
  where
    module M = Monoid M
