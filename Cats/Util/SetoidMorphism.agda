{-# OPTIONS --without-K --safe #-}
module Cats.Util.SetoidMorphism where

open import Data.Product using (∃-syntax ; _,_ ; proj₁ ; proj₂)
open import Level using (_⊔_ ; suc)
open import Relation.Binary using (Rel ; Setoid ; IsEquivalence ; _Preserves_⟶_)
open import Relation.Binary.SetoidReasoning

open import Cats.Util.Function using () renaming (_∘_ to _⊚_)

open Setoid renaming (_≈_ to eq)


infixr 9 _∘_


record _⇒_ {l l≈} (A : Setoid l l≈) {l′ l≈′} (B : Setoid l′ l≈′)
  : Set (l ⊔ l′ ⊔ l≈ ⊔ l≈′)
  where
  field
    arr : Carrier A → Carrier B
    resp : arr Preserves eq A ⟶ eq B

open _⇒_ public using (arr ; resp)


module _ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′} where

  infixr 4 _≈_


  record _≈_ (f g : A ⇒ B) : Set (l ⊔ l≈ ⊔ l≈′) where
    constructor ≈-intro
    field
       ≈-elim : ∀ {x y} → eq A x y → eq B (arr f x) (arr g y)

    ≈-elim′ : ∀ {x} → eq B (arr f x) (arr g x)
    ≈-elim′ = ≈-elim (refl A)

  open _≈_ public


  equiv : IsEquivalence _≈_
  equiv = record
      { refl = λ {f} → ≈-intro (resp f)
      ; sym = λ eq → ≈-intro λ x≈y → sym B (≈-elim eq (sym A x≈y))
      ; trans = λ eq₁ eq₂ → ≈-intro (λ x≈y → trans B (≈-elim eq₁ x≈y) (≈-elim′ eq₂))
      }


  setoid : Setoid (l ⊔ l≈ ⊔ l′ ⊔ l≈′) (l ⊔ l≈ ⊔ l≈′)
  setoid = record
      { Carrier = A ⇒ B
      ; _≈_ = _≈_
      ; isEquivalence = equiv
      }


id : ∀ {l l≈} {A : Setoid l l≈} → A ⇒ A
id = record { arr = λ x → x ; resp = λ x → x }


_∘_ : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  → ∀ {l″ l≈″} {C : Setoid l″ l≈″}
  → B ⇒ C → A ⇒ B → A ⇒ C
_∘_ f g = record
    { arr = arr f ⊚ arr g
    ; resp = resp f ⊚ resp g
    }


∘-resp : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  → ∀ {l″ l≈″} {C : Setoid l″ l≈″}
  → {f f′ : B ⇒ C} {g g′ : A ⇒ B}
  → f ≈ f′ → g ≈ g′ → f ∘ g ≈ f′ ∘ g′
∘-resp f≈f′ g≈g′ = ≈-intro (≈-elim f≈f′ ⊚ ≈-elim g≈g′)


id-l : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
   → {f : A ⇒ B}
   → id ∘ f ≈ f
id-l {f = f} = ≈-intro (resp f)


id-r : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  → {f : A ⇒ B}
  → f ∘ id ≈ f
id-r {f = f} = ≈-intro (resp f)


assoc : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  → ∀ {l″ l≈″} {C : Setoid l″ l≈″} {l‴ l≈‴} {D : Setoid l‴ l≈‴}
  → {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
  → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
assoc {f = f} {g} {h} = ≈-intro (resp f ⊚ resp g ⊚ resp h)


module _ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′} where

  IsInjective : A ⇒ B → Set (l ⊔ l≈ ⊔ l≈′)
  IsInjective f = ∀ {a b} → eq B (arr f a) (arr f b) → eq A a b


  IsSurjective : A ⇒ B → Set (l ⊔ l′ ⊔ l≈′)
  IsSurjective f = ∀ b → ∃[ a ] (eq B b (arr f a))
