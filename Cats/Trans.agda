module Cats.Trans where

open import Level using (_⊔_)

open import Cats.Category.Base
open import Cats.Functor using (Functor)

open Functor


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  infixr 9 _∘_


  private
    module C = Category C
    module D = Category D
    open D.≈-Reasoning


  record Trans (F G : Functor C D) : Set (lo ⊔ la ⊔ la′ ⊔ l≈′) where
    field
      component : (c : C.Obj) → fobj F c D.⇒ fobj G c
      natural : ∀ {c d} {f : c C.⇒ d}
        → component d D.∘ fmap F f D.≈ fmap G f D.∘ component c

  open Trans public


  id : ∀ {F} → Trans F F
  id {F} = record
      { component = λ _ → D.id
      ; natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
      }


  _∘_ : ∀ {F G H} → Trans G H → Trans F G → Trans F H
  _∘_ {F} {G} {H} θ ι = record
      { component = λ c → component θ c D.∘ component ι c
      ; natural = λ {c} {d} {f} →
          begin
            (component θ d D.∘ component ι d) D.∘ fmap F f
          ≈⟨ D.assoc ⟩
            component θ d D.∘ component ι d D.∘ fmap F f
          ≈⟨ D.∘-resp-r (natural ι) ⟩
            component θ d D.∘ fmap G f D.∘ component ι c
          ≈⟨ D.unassoc ⟩
            (component θ d D.∘ fmap G f) D.∘ component ι c
          ≈⟨ D.∘-resp-l (natural θ)  ⟩
            (fmap H f D.∘ component θ c) D.∘ component ι c
          ≈⟨ D.assoc ⟩
            fmap H f D.∘ component θ c D.∘ component ι c
          ∎
      }
