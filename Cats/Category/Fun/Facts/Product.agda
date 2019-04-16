module Cats.Category.Fun.Facts.Product where

open import Data.Product using (_,_)

open import Cats.Category
open import Cats.Category.Fun as Fun using (Fun)
open import Cats.Category.Constructions.Product using (HasBinaryProducts)
open import Cats.Functor using (Functor)
open import Cats.Trans using (Trans)

open Functor
open Trans


module Build {lo la l≈ lo′ la′ l≈′}
  (C : Category lo la l≈) (D : Category lo′ la′ l≈′)
  {{D× : HasBinaryProducts D}}
  where

  infixr 2 _×_ _×′_ ⟨_,_⟩


  private
    module D = Category D
    module D× = HasBinaryProducts D×
    open D.≈
    open Category (Fun C D)


  _×_ : (F G : Obj) → Obj
  F × G = record
    { fobj = λ c → fobj F c D×.× fobj G c
    ; fmap = λ f → D×.⟨ fmap F f × fmap G f ⟩
    ; fmap-resp = λ f≈g → D×.⟨×⟩-resp (fmap-resp F f≈g) (fmap-resp G f≈g)
    ; fmap-id = trans (D×.⟨×⟩-resp (fmap-id F) (fmap-id G)) D×.⟨×⟩-id
    ; fmap-∘ = trans D×.⟨×⟩-∘ (D×.⟨×⟩-resp (fmap-∘ F) (fmap-∘ G))
    }


  projl : ∀ {F G} → F × G ⇒ F
  projl = record
    { component = λ c → D×.projl
    ; natural = D×.⟨×⟩-projl
    }


  projr : ∀ {F G} → F × G ⇒ G
  projr = record
    { component = λ c → D×.projr
    ; natural = D×.⟨×⟩-projr
    }


  ⟨_,_⟩ : ∀ {F G X} → X ⇒ F → X ⇒ G → X ⇒ F × G
  ⟨_,_⟩ α β = record
    { component = λ c → D×.⟨ component α c , component β c ⟩
    ; natural = λ {c} {d} {f} →
        trans D×.⟨,⟩-∘
          (trans (D×.⟨,⟩-resp (natural α) (natural β))
            (sym D×.⟨×⟩-⟨,⟩))
    }


  ⟨,⟩-projl : ∀ {F G X} {α : X ⇒ F} (β : X ⇒ G)
    → α ≈ projl ∘ ⟨ α , β ⟩
  ⟨,⟩-projl β = Fun.≈-intro (sym D×.⟨,⟩-projl)


  ⟨,⟩-projr : ∀ {F G X} (α : X ⇒ F) {β : X ⇒ G}
    → β ≈ projr ∘ ⟨ α , β ⟩
  ⟨,⟩-projr α = Fun.≈-intro (sym D×.⟨,⟩-projr)


  ⟨,⟩-unique : ∀ {F G X} {α : X ⇒ F} {β : X ⇒ G} {u}
    → α ≈ projl ∘ u
    → β ≈ projr ∘ u
    → ⟨ α , β ⟩ ≈ u
  ⟨,⟩-unique (Fun.≈-intro pl) (Fun.≈-intro pr)
    = Fun.≈-intro (D×.⟨,⟩-unique pl pr)


  isBinaryProduct : ∀ {F G} → IsBinaryProduct (F × G) projl projr
  isBinaryProduct α β = record
    { arr = ⟨ α , β ⟩
    ; prop = (⟨,⟩-projl β , ⟨,⟩-projr α)
    ; unique = λ { (eql , eqr) → ⟨,⟩-unique eql eqr }
    }


  _×′_ : (F G : Obj) → BinaryProduct F G
  F ×′ G = mkBinaryProduct projl projr isBinaryProduct

private
  open module Build′ {lo la l≈ lo′ la′ l≈′}
    {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
    = Build C D
    public


instance
  hasBinaryProducts : ∀ {lo la l≈ lo′ la′ l≈′}
    → {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
    → {{D× : HasBinaryProducts D}}
    → HasBinaryProducts (Fun C D)
  hasBinaryProducts = record { _×′_ = _×′_ }
