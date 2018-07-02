module Cats.Category.Mon where

open import Data.Unit using (⊤)
open import Relation.Binary using (Setoid ; _Preserves₂_⟶_⟶_ ; IsEquivalence)
open import Level

open import Cats.Category
open import Cats.Category.Setoids using (Setoids)
open import Cats.Util.Conv

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


  module Setoids = Category (Setoids l l≈)


  Obj : Set (suc (l ⊔ l≈))
  Obj = Monoid l l≈


  record _⇒_ (M N : Obj) : Set (l ⊔ l≈) where
    private
      module M = Monoid M
      module N = Monoid N

    field
      arr : M.Universe Setoids.⇒ N.Universe
      unit : (arr ⃗) M.unit N.≈ N.unit
      commute : ∀ {n m} → (arr ⃗) (n M.⊕ m) N.≈ (arr ⃗) n N.⊕ (arr ⃗) m

    open Cats.Category.Setoids._⇒_ arr public using (resp)

  open _⇒_ using (unit ; commute ; resp)


  instance
    HasArrow-⇒ : ∀ M N → HasArrow (M ⇒ N) _ _ _
    HasArrow-⇒ M N = record { Cat = Setoids l l≈ ; _⃗ = _⇒_.arr }


  id : ∀ {M} → M ⇒ M
  id {M} = record
      { arr = Setoids.id
      ; unit = refl
      ; commute = refl
      }
    where
      open Monoid M using (refl)


  _≈_ : ∀ {M N} (f g : M ⇒ N) → Set (l≈ ⊔ l)
  _≈_ = Setoids._≈_ Fun.on _⃗


  equiv : ∀ {M N} → IsEquivalence (_≈_ {M} {N})
  equiv = Fun.on-isEquivalence _⃗ Setoids.equiv


  _∘_ : ∀ {M N O} → (N ⇒ O) → (M ⇒ N) → (M ⇒ O)
  _∘_ {M} {N} {O} f g = record
      { arr = f ⃗ Setoids.∘ g ⃗
      ; unit = trans (resp f (unit g)) (unit f)
      ; commute = trans (resp f (commute g)) (commute f)
      }
    where
      open Monoid O using (trans)


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
