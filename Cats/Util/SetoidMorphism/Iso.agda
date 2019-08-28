{-# OPTIONS --without-K --safe #-}
module Cats.Util.SetoidMorphism.Iso where

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Level using (_⊔_)
open import Relation.Binary using (Setoid ; IsEquivalence)

open import Cats.Util.SetoidMorphism as Mor using
  ( _⇒_ ; arr ; resp ; _≈_ ; ≈-intro ; ≈-elim ; ≈-elim′ ; _∘_ ; ∘-resp ; id
  ; IsInjective ; IsSurjective )
open import Cats.Util.SetoidReasoning


private
  module S = Setoid


record IsIso {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  (f : A ⇒ B) : Set (l ⊔ l≈ ⊔ l′ ⊔ l≈′)
  where
  field
    back : B ⇒ A
    forth-back : f ∘ back ≈ id
    back-forth : back ∘ f ≈ id

open IsIso


record _≅_ {l l≈} (A : Setoid l l≈) {l′ l≈′} (B : Setoid l′ l≈′)
  : Set (l ⊔ l≈ ⊔ l′ ⊔ l≈′)
  where
  field
    forth : A ⇒ B
    back : B ⇒ A
    forth-back : forth ∘ back ≈ id
    back-forth : back ∘ forth ≈ id

open _≅_ public


IsIso→≅ : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′} (f : A ⇒ B)
  → IsIso f → A ≅ B
IsIso→≅ f i = record
    { forth = f
    ; back = back i
    ; forth-back = forth-back i
    ; back-forth = back-forth i
    }


≅→IsIso : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  → (i : A ≅ B) → IsIso (forth i)
≅→IsIso i = record
    { back = back i
    ; forth-back = forth-back i
    ; back-forth = back-forth i
    }


IsIso-resp : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  → {f g : A ⇒ B} → f ≈ g → IsIso f → IsIso g
IsIso-resp {A = A} {B = B} {f} {g} f≈g i = record
    { back = back i
    ; forth-back = ≈-intro λ {x} {y} x≈y →
        begin⟨ B ⟩
          arr g (arr (back i) x)
        ≈˘⟨ ≈-elim f≈g (resp (back i) (B.sym x≈y)) ⟩
          arr f (arr (back i) y)
        ≈⟨ ≈-elim′ (forth-back i) ⟩
          y
        ∎
    ; back-forth = ≈-intro λ {x} {y} x≈y →
        begin⟨ A ⟩
          arr (back i) (arr g x)
        ≈⟨ resp (back i) (B.sym (≈-elim f≈g (A.sym x≈y))) ⟩
          arr (back i) (arr f y)
        ≈⟨ ≈-elim′ (back-forth i) ⟩
          y
        ∎
    }
  where
    module A = Setoid A
    module B = Setoid B


refl : ∀ {l l≈} {A : Setoid l l≈} → A ≅ A
refl = record
    { forth = id
    ; back = id
    ; forth-back = ≈-intro λ eq → eq
    ; back-forth = ≈-intro λ eq → eq
    }


sym : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  → A ≅ B → B ≅ A
sym i = record
    { forth = back i
    ; back = forth i
    ; forth-back = back-forth i
    ; back-forth = forth-back i
    }


trans : ∀ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′}
  → ∀ {l″ l≈″} {C : Setoid l″ l≈″}
  → A ≅ B → B ≅ C → A ≅ C
trans {A = A} {C = C} AB BC = record
    { forth = forth BC ∘ forth AB
    ; back = back AB ∘ back BC
    ; forth-back = ≈-intro λ x≈y
        → S.trans C (resp (forth BC) (≈-elim (forth-back AB) (resp (back BC) x≈y)))
            (≈-elim′ (forth-back BC))
    ; back-forth = ≈-intro λ x≈y
        → S.trans A (resp (back AB) (≈-elim (back-forth BC) (resp (forth AB) x≈y)))
            (≈-elim′ (back-forth AB))
    }


module _ {l l≈} {A : Setoid l l≈} {l′ l≈′} {B : Setoid l′ l≈′} where

  Injective∧Surjective→Iso : {f : A ⇒ B}
    → IsInjective f → IsSurjective f → IsIso f
  Injective∧Surjective→Iso {f} inj surj = record
      { back = record
        { arr = λ b → proj₁ (surj b)
        ; resp = λ {b} {c} b≈c → inj
            (S.trans B (S.sym B (proj₂ (surj b))) (S.trans B b≈c (proj₂ (surj c))))
        }
      ; forth-back = ≈-intro λ {x} {y} x≈y → S.trans B (S.sym B (proj₂ (surj x))) x≈y
      ; back-forth = ≈-intro λ {x} {y} x≈y → inj
          (S.trans B (S.sym B (proj₂ (surj _))) (resp f x≈y))
      }


  Injective∧Surjective→≅ : {f : A ⇒ B} → IsInjective f → IsSurjective f → A ≅ B
  Injective∧Surjective→≅ {f} inj surj
      = IsIso→≅ f (Injective∧Surjective→Iso inj surj)


  Iso→Injective : {f : A ⇒ B} → IsIso f → IsInjective f
  Iso→Injective {f} i {a} {b} fa≈fb =
      begin⟨ A ⟩
        a
      ≈˘⟨ ≈-elim′ (back-forth i) ⟩
        arr (back i) (arr f a)
      ≈⟨ resp (back i) fa≈fb ⟩
        arr (back i) (arr f b)
      ≈⟨ ≈-elim′ (back-forth i) ⟩
        b
      ∎


  ≅-Injective : (i : A ≅ B) → IsInjective (forth i)
  ≅-Injective i = Iso→Injective (≅→IsIso i)


  Iso→Surjective : {f : A ⇒ B} → IsIso f → IsSurjective f
  Iso→Surjective i b = arr (back i) b  , S.sym B (≈-elim′ (forth-back i))


  ≅-Surjective : (i : A ≅ B) → IsSurjective (forth i)
  ≅-Surjective i = Iso→Surjective (≅→IsIso i)
