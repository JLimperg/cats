module Cats.Displayed where

open import Data.Product using (Σ ; Σ-syntax ; _,_)
open import Level using (_⊔_ ; suc)
open import Relation.Binary using
  (Setoid ; IsEquivalence ; Rel ; REL ; _Preserves₂_⟶_⟶_)

open import Cats.Category


record DisplayedCategory {lo la l≈} (C : Category lo la l≈) lo′ la′ l≈′
  : Set (lo ⊔ la ⊔ l≈ ⊔ suc (lo′ ⊔ la′ ⊔ l≈′)) where
  infixr  9  _∘_
  infix   4  _≈[_]_
  infixr  -1 _⇒[_]_

  Base = C
  module Base = Category Base
  private
    module C = Category C

  field
    Obj : (c : C.Obj) → Set lo′
    _⇒[_]_ : ∀ {a b} (a⁺ : Obj a) (f : a C.⇒ b) (b⁺ : Obj b) → Set la′
    _≈[_]_ : ∀ {a b} {f g : a C.⇒ b} {a⁺ : Obj a} {b⁺ : Obj b}
      → a⁺ ⇒[ f ] b⁺
      → f C.≈ g
      → a⁺ ⇒[ g ] b⁺
      → Set l≈′
    id : ∀ {a} {a⁺ : Obj a} → a⁺ ⇒[ C.id ] a⁺
    _∘_ : ∀ {a b c} {a⁺ : Obj a} {b⁺ : Obj b} {c⁺ : Obj c}
      → {f : b C.⇒ c} {g : a C.⇒ b}
      → (f⁺ : b⁺ ⇒[ f ] c⁺) (g⁺ : a⁺ ⇒[ g ] b⁺)
      → a⁺ ⇒[ f C.∘ g ] c⁺
    ≈-refl : ∀ {a b} {f : a C.⇒ b} {a⁺ : Obj a} {b⁺ : Obj b} {f⁺ : a⁺ ⇒[ f ] b⁺}
      → f⁺ ≈[ C.≈.refl ] f⁺
    ≈-sym : ∀ {a b} {f g : a C.⇒ b} {f≈g : f C.≈ g} {a⁺ : Obj a} {b⁺ : Obj b}
      → {f⁺ : a⁺ ⇒[ f ] b⁺} {g⁺ : a⁺ ⇒[ g ] b⁺}
      → f⁺ ≈[ f≈g ] g⁺
      → g⁺ ≈[ C.≈.sym f≈g ] f⁺
    ≈-trans : ∀ {a b}
      → {f g h : a C.⇒ b} {f≈g : f C.≈ g} {g≈h : g C.≈ h}
      → {a⁺ : Obj a} {b⁺ : Obj b}
      → {f⁺ : a⁺ ⇒[ f ] b⁺} {g⁺ : a⁺ ⇒[ g ] b⁺} {h⁺ : a⁺ ⇒[ h ] b⁺}
      → f⁺ ≈[ f≈g ] g⁺ → g⁺ ≈[ g≈h ] h⁺
      → f⁺ ≈[ C.≈.trans f≈g g≈h ] h⁺
    ∘-resp : ∀ {a b c} {f g : b C.⇒ c} {h i : a C.⇒ b}
      → {f≈g : f C.≈ g} {h≈i : h C.≈ i}
      → {a⁺ : Obj a} {b⁺ : Obj b} {c⁺ : Obj c}
      → {f⁺ : b⁺ ⇒[ f ] c⁺} {g⁺ : b⁺ ⇒[ g ] c⁺}
      → {h⁺ : a⁺ ⇒[ h ] b⁺} {i⁺ : a⁺ ⇒[ i ] b⁺}
      → f⁺ ≈[ f≈g ] g⁺
      → h⁺ ≈[ h≈i ] i⁺
      → f⁺ ∘ h⁺ ≈[ C.∘-resp f≈g h≈i ] g⁺ ∘ i⁺
    id-r : ∀ {a b} {f : a C.⇒ b} {a⁺ : Obj a} {b⁺ : Obj b} {f⁺ : a⁺ ⇒[ f ] b⁺}
      → f⁺ ∘ id ≈[ C.id-r ] f⁺
    id-l : ∀ {a b} {f : a C.⇒ b} {a⁺ : Obj a} {b⁺ : Obj b} {f⁺ : a⁺ ⇒[ f ] b⁺}
      → id ∘ f⁺ ≈[ C.id-l ] f⁺
    assoc : ∀ {a b c d} {f : c C.⇒ d} {g : b C.⇒ c} {h : a C.⇒ b}
      → {a⁺ : Obj a} {b⁺ : Obj b} {c⁺ : Obj c} {d⁺ : Obj d}
      → {f⁺ : c⁺ ⇒[ f ] d⁺} {g⁺ : b⁺ ⇒[ g ] c⁺} {h⁺ : a⁺ ⇒[ h ] b⁺}
      → (f⁺ ∘ g⁺) ∘ h⁺ ≈[ C.assoc ] f⁺ ∘ (g⁺ ∘ h⁺)


module BuildTotal
  {lo la l≈} {C : Category lo la l≈} {lo′ la′ l≈′}
  (D : DisplayedCategory C lo′ la′ l≈′)
  where

  infixr  9  _∘_
  infix   4  _≈_
  infixr  -1 _⇒_

  private
    module C = Category C
    module D = DisplayedCategory D


  Obj : Set (lo ⊔ lo′)
  Obj = Σ[ c ∈ C.Obj ] D.Obj c


  _⇒_ : (a b : Obj) → Set (la ⊔ la′)
  (a , a⁺) ⇒ (b , b⁺) = Σ[ f ∈ a C.⇒ b ] (a⁺ D.⇒[ f ] b⁺)


  _≈_ : ∀ {a b} → Rel (a ⇒ b) (l≈ ⊔ l≈′)
  (f , f⁺) ≈ (g , g⁺) = Σ[ f≈g ∈ f C.≈ g ] f⁺ D.≈[ f≈g ] g⁺


  id : ∀ {a} → a ⇒ a
  id = C.id , D.id


  _∘_ : ∀ {a b c} → b ⇒ c → a ⇒ b → a ⇒ c
  (f , f⁺) ∘ (g , g⁺) = (f C.∘ g) , (f⁺ D.∘ g⁺)


  equiv : ∀ {a b} → IsEquivalence (_≈_ {a} {b})
  equiv = record
    { refl = C.≈.refl , D.≈-refl
    ; sym = λ where
        (f≈g , f⁺≈g⁺) → C.≈.sym f≈g , D.≈-sym f⁺≈g⁺
    ; trans = λ where
        (f≈g , f⁺≈g⁺) (g≈h , g⁺≈h⁺) → C.≈.trans f≈g g≈h , D.≈-trans f⁺≈g⁺ g⁺≈h⁺
    }


  ∘-resp : ∀ {a b c} → (_∘_ {a} {b} {c} Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_)
  ∘-resp (f≈g , f⁺≈g⁺) (h≈i , h⁺≈i⁺) = C.∘-resp f≈g h≈i , D.∘-resp f⁺≈g⁺ h⁺≈i⁺


  id-r : ∀ {a b} {f : a ⇒ b} → f ∘ id ≈ f
  id-r = C.id-r , D.id-r


  id-l : ∀ {a b} {f : a ⇒ b} → id ∘ f ≈ f
  id-l = C.id-l , D.id-l


  assoc : ∀ {a b c d} {f : c ⇒ d} {g : b ⇒ c} {h : a ⇒ b}
    → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
  assoc = C.assoc , D.assoc


  Total : Category (lo ⊔ lo′) (la ⊔ la′) (l≈ ⊔ l≈′)
  Total = record
    { Obj = Obj
    ; _⇒_ = _⇒_
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = _∘_
    ; equiv = equiv
    ; ∘-resp = ∘-resp
    ; id-r = id-r
    ; id-l = id-l
    ; assoc = assoc
    }

open BuildTotal public using (Total)
