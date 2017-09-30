module Cats.Category.Mon where

open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Level using (Level ; zero ; suc)

open import Cats.Category
open import Cats.Util.Function as Fun using (_on_ ; on-isEquivalence)

import Cats.Util.ExtensionalEquality.Propositional as Fun


-- TODO hardcoding propositional equality here, but I can't be arsed
-- TODO this cries for abstraction: A family of categories of structured sets?
record Monoid l : Set (suc l) where
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


  Obj : Set (suc l)
  Obj = Monoid l


  record _⇒_ (M N : Obj) : Set (suc l) where
    private
      module M = Monoid M
      module N = Monoid N

    field
      arr : M.Carrier → N.Carrier
      unit : arr M.unit ≡ N.unit
      lift : ∀ {n m} → arr (n M.⊕ m) ≡ arr n N.⊕ arr m

  open _⇒_


  id : ∀ {M} → M ⇒ M
  id = record { arr = Fun.id ; unit = ≡.refl ; lift = ≡.refl }


  _≈_ : ∀ {M N} (f g : M ⇒ N) → Set l
  _≈_ = Fun._≈_ on arr


  _∘_ : ∀ {M N O} → (N ⇒ O) → (M ⇒ N) → (M ⇒ O)
  f ∘ g = record
    { arr = arr f Fun.∘ arr g
    ; unit = ≡.trans (≡.cong (arr f) (unit g)) (unit f)
    ; lift = ≡.trans (≡.cong (arr f) (lift g)) (lift f)
    }


  Mon : Category (suc l) (suc l) l
  Mon = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = on-isEquivalence arr Fun.isEquivalence
      ; ∘-resp = Fun.∘-resp
      ; id-r = Fun.∘-id-r
      ; id-l = Fun.∘-id-l
      ; assoc = λ h g f x → Fun.∘-assoc (arr h) (arr g) (arr f) x
      }


monoidAsCategory : ∀ {l} → Monoid l → Category zero l l
monoidAsCategory M = record
    { Obj = ⊤
    ; _⇒_ = λ _ _ → M.Carrier
    ; _≈_ = _≡_
    ; id = M.unit
    ; _∘_ = M._⊕_
    ; equiv = ≡.isEquivalence
    ; ∘-resp = ≡.cong₂ M._⊕_
    ; id-r = M.id-r
    ; id-l = M.id-l
    ; assoc = M.assoc
    }
  where
    module M = Monoid M
