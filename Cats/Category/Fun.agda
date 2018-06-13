module Cats.Category.Fun where

open import Cats.Trans public using (Trans ; component ; natural ; id ; _∘_)


open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Level

open import Cats.Category
open import Cats.Functor using (Functor)

module _ {lo la l≈ lo′ la′ l≈′}
  (C : Category lo la l≈)
  (D : Category lo′ la′ l≈′)
  where

  infixr 4 _≈_


  private
    module C = Category C
    module D = Category D
    open D.≈
    open D.≈-Reasoning


  Obj : Set (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′)
  Obj = Functor C D


  _⇒_ : Obj → Obj → Set (lo ⊔ la ⊔ la′ ⊔ l≈′)
  _⇒_ = Trans


  _≈_ : ∀ {F G} → Rel (F ⇒ G) (lo ⊔ l≈′)
  θ ≈ ι = ∀ c → component θ c D.≈ component ι c


  equiv : ∀ {F G} → IsEquivalence (_≈_ {F} {G})
  equiv = record
      { refl = λ _ → refl
      ; sym = λ eq c → sym (eq c)
      ; trans = λ eq₁ eq₂ c → trans (eq₁ c) (eq₂ c)
      }


  Fun : Category (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′) (lo ⊔ la ⊔ la′ ⊔ l≈′) (lo ⊔ l≈′)
  Fun = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = λ θ≈θ′ ι≈ι′ c → D.∘-resp (θ≈θ′ c) (ι≈ι′ c)
      ; id-r = λ _ → D.id-r
      ; id-l = λ _ → D.id-l
      ; assoc = λ _ → D.assoc
      }
