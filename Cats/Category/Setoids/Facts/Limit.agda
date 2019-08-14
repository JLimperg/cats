module Cats.Category.Setoids.Facts.Limit where

open import Level using (_⊔_)
open import Relation.Binary using (Setoid)

open import Cats.Category
open import Cats.Category.Cones as Cones using (Cone)
open import Cats.Category.Setoids as Setoids using (Setoids ; ≈-intro ; ≈-elim)
open import Cats.Functor using (Functor)

open Cone
open Cones._⇒_
open Functor
open Setoid using (Carrier)
open Setoids._⇒_


record Lim {l} {J : Category l l l} (F : Functor J (Setoids l l)) : Set l where
  private
    module J = Category J
    module F$ {x} = Setoid (F .fobj x)

  field
    arr : ∀ j → F .fobj j .Carrier
    consistent : ∀ {i j} (f : i J.⇒ j)
      → arr j F$.≈ F .fmap f .Setoids._⇒_.arr (arr i)

open Lim public


instance
  complete : ∀ {l} → Complete (Setoids l l) l l l
  complete .Complete.lim′ {J} F = record
    { cone = record
      { Apex = record
        { Carrier = Lim F
        ; _≈_ = λ f g → ∀ j → f .arr j F$.≈ g .arr j
        ; isEquivalence = record
          { refl = λ j → F$.refl
          ; sym = λ eq j → F$.sym (eq j)
          ; trans = λ eq₁ eq₂ j → F$.trans (eq₁ j) (eq₂ j)
          }
        }
      ; arr = λ j → record { resp = λ eq → eq j }
      ; commute = λ h → ≈-intro λ {f} {g} f≈g → F$.trans (f≈g _) (g .consistent h)
      }
    ; isLimit = λ X → record
      { arr = record
        { arr = record
          { arr = λ x → record
            { arr = λ j → X .arr j .arr x
            ; consistent = λ f → X .commute f .≈-elim (Setoid.refl (Apex X))
            }
          ; resp = λ eq j → X .arr j .resp eq
          }
        ; commute = λ j → ≈-intro λ eq → X .arr j .resp eq
        }
      ; unique = λ {g} _ → ≈-intro λ eq j
          → F$.sym (g .commute j .≈-elim (Setoid.sym (Apex X) eq))
      }
    }
    where
      module F$ {x} = Setoid (F .fobj x)
