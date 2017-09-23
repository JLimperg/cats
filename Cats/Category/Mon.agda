module Cats.Category.Mon where

open import Data.Unit using (⊤ ; tt)
open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Level using (Level) renaming (zero to lzero ; suc to lsuc)

open import Cats.Category

-- TODO hardcoding propositional equality here, but I can't be arsed
-- TODO this cries for abstraction: A family of categories of structured sets?
record Monoid l : Set (lsuc l) where
  infixr 9 _⊕_

  field
    Carrier : Set l
    _⊕_ : Carrier → Carrier → Carrier
    unit : Carrier

    assoc : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
    id-l : ∀ {a} → unit ⊕ a ≡ a
    id-r : ∀ {a} → a ⊕ unit ≡ a


module _ (l : Level) where

  infixr 9 _∘_
  infixr 4 _≈_


  Obj : Set (lsuc l)
  Obj = Monoid l


  record _⇒_ (M N : Obj) : Set (lsuc l) where
    private
      module M = Monoid M
      module N = Monoid N

    field
      arr : M.Carrier → N.Carrier
      unit : arr M.unit ≡ N.unit
      lift : ∀ {n m} → arr (n M.⊕ m) ≡ arr n N.⊕ arr m

  open _⇒_


  id : ∀ {M} → M ⇒ M
  id = record { arr = λ x → x ; unit = ≡.refl ; lift = ≡.refl }


  record _≈_ {M N} (f g : M ⇒ N) : Set l where
    constructor ≈-i
    field eq : ∀ {x} → arr f x ≡ arr g x


  ≈-equiv : ∀ {M N} → IsEquivalence (_≈_ {M} {N})
  ≈-equiv = record
      { refl = ≈-i ≡.refl
      ; sym = λ { (≈-i eq) → ≈-i (≡.sym eq) }
      ; trans = λ { (≈-i eq₁) (≈-i eq₂) → ≈-i (≡.trans eq₁ eq₂) }
      }


  _∘_ : ∀ {M N O} → (N ⇒ O) → (M ⇒ N) → (M ⇒ O)
  _∘_ f g = record
    { arr = λ x → arr f (arr g x)
    ; unit = ≡.trans (≡.cong (arr f) (unit g)) (unit f)
    ; lift = ≡.trans (≡.cong (arr f) (lift g)) (lift f)
    }


  ∘-preserves-≈ : ∀ {M N O} → _∘_ {M} {N} {O} Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ∘-preserves-≈ {x = f} {g} {h} {i} (≈-i f≈g) (≈-i h≈i)
      = ≈-i (≡.trans f≈g (≡.cong (arr g) h≈i))


  id-identity-r : ∀ {M N} {f : M ⇒ N} → f ∘ id ≈ f
  id-identity-r = ≈-i ≡.refl


  id-identity-l : ∀ {M N} {f : M ⇒ N} → id ∘ f ≈ f
  id-identity-l = ≈-i ≡.refl


  ∘-assoc : ∀ {M N O P} (f : O ⇒ P) (g : N ⇒ O) (h : M ⇒ N)
    → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
  ∘-assoc _ _ _ = ≈-i ≡.refl


  Mon : Category (lsuc l) (lsuc l) l
  Mon = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; ≈-equiv = ≈-equiv
      ; ∘-preserves-≈ = ∘-preserves-≈
      ; id-identity-r = id-identity-r
      ; id-identity-l = id-identity-l
      ; ∘-assoc = ∘-assoc
      }


monoidAsCategory : ∀ {l} → Monoid l → Category lzero l l
monoidAsCategory M = record
    { Obj = ⊤
    ; _⇒_ = λ _ _ → Carrier
    ; _≈_ = _≡_
    ; id = unit
    ; _∘_ = _⊕_
    ; ≈-equiv = ≡.isEquivalence
    ; ∘-preserves-≈ = ≡.cong₂ _⊕_
    ; id-identity-r = id-r
    ; id-identity-l = id-l
    ; ∘-assoc = assoc
    }
  where
    open Monoid M
