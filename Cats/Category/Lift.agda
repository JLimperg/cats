module Cats.Category.Lift where

open import Relation.Binary using (IsEquivalence)
open import Level as L using (Level ; suc ; _⊔_ ; lift ; lower)

open import Cats.Category.Base

open IsEquivalence


LCategory : (l : Level) → Set (suc l)
LCategory l = Category l l l


Lift : ∀ {lo la l≈ lo′ la′ l≈′} → Category lo la l≈
  → Category (lo ⊔ lo′) (la ⊔ la′) (l≈ ⊔ l≈′)
Lift {lo′ = lo′} {la′} {l≈′} C = record
    { Obj = L.Lift {ℓ = lo′} C.Obj
    ; _⇒_ = λ A B → L.Lift {ℓ = la′} (lower A C.⇒ lower B)
    ; _≈_ = λ f g → L.Lift {ℓ = l≈′} (lower f C.≈ lower g)
    ; id = lift C.id
    ; _∘_ = λ f g → lift (lower f C.∘ lower g)
    ; equiv = record
        { refl = lift (refl C.equiv)
        ; sym = λ eq → lift (sym C.equiv (lower eq))
        ; trans = λ eq₁ eq₂ → lift (trans C.equiv (lower eq₁) (lower eq₂))
        }
    ; ∘-resp = λ eq₁ eq₂ → lift (C.∘-resp (lower eq₁) (lower eq₂))
    ; id-r = lift C.id-r
    ; id-l = lift C.id-l
    ; assoc = lift C.assoc
    }
  where
    module C = Category C


LiftEq : ∀ {lo la l≈} → Category lo la l≈
  → LCategory (lo ⊔ la ⊔ l≈)
LiftEq {lo} {la} {l≈} = Lift {lo′ = la ⊔ l≈} {la′ = lo ⊔ l≈} {l≈′ = lo ⊔ la}
