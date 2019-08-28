{-# OPTIONS --without-K --safe #-}
module Cats.Category.Fun where

open import Cats.Trans public using (Trans ; component ; natural ; id ; _∘_)


open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Level

open import Cats.Category.Base
open import Cats.Functor using (Functor)


module Build {lo la l≈ lo′ la′ l≈′}
  (C : Category lo la l≈)
  (D : Category lo′ la′ l≈′)
  where

  infixr 4 _≈_
  infixr -1 _↝_


  private
    module C = Category C
    module D = Category D
    open D.≈
    open D.≈-Reasoning


  Obj : Set (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′)
  Obj = Functor C D


  _⇒_ : Obj → Obj → Set (lo ⊔ la ⊔ la′ ⊔ l≈′)
  _⇒_ = Trans


  record _≈_ {F G} (θ ι : F ⇒ G) : Set (lo ⊔ l≈′) where
    constructor ≈-intro
    field
      ≈-elim : ∀ {c} → component θ c D.≈ component ι c

  open _≈_ public


  equiv : ∀ {F G} → IsEquivalence (_≈_ {F} {G})
  equiv = record
      { refl = ≈-intro refl
      ; sym = λ eq → ≈-intro (sym (≈-elim eq))
      ; trans = λ eq₁ eq₂ → ≈-intro (trans (≈-elim eq₁) (≈-elim eq₂))
      }


  Fun : Category (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′) (lo ⊔ la ⊔ la′ ⊔ l≈′) (lo ⊔ l≈′)
  Fun = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = λ θ≈θ′ ι≈ι′ → ≈-intro (D.∘-resp (≈-elim θ≈θ′) (≈-elim ι≈ι′))
      ; id-r = ≈-intro D.id-r
      ; id-l = ≈-intro D.id-l
      ; assoc = ≈-intro D.assoc
      }

  _↝_ = Fun


open Build public using (Fun ; _↝_)


open module Build′
  {lo la l≈ lo′ la′ l≈′} {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  = Build C D public
  hiding (Fun ; _↝_)
