{-# OPTIONS --without-K --safe #-}
module Cats.Category.Fun.Facts.Limit where

open import Data.Product using (_,_)

open import Cats.Category
open import Cats.Category.Cat.Facts.Exponential using (Eval ; Curry ; Uncurry)
open import Cats.Category.Cat.Facts.Product using (Swap)
open import Cats.Category.Cones as Cones using (Cone ; Apex ; arr ; commute)
open import Cats.Category.Fun using (≈-intro ; ≈-elim) renaming (Fun to _↝_)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Functor using (Functor ; _∘_)
open import Cats.Limit using (Limit ; IsLimit ; Complete ; trans ; arr∘trans)
open import Cats.Trans using (Trans ; component ; natural)

open Functor
open Limit


instance
  -- Good lord this proof...
  complete : ∀ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
    → {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
    → {{_ : Complete D lo″ la″ l≈″}}
    → Complete (C ↝ D) lo″ la″ l≈″
  complete {C = C} {D} {{D-complete}} .Complete.lim′ {J} F = record
    { cone = record
      { Apex = DC.limF ∘ F′
      ; arr = λ j → record
        { component = λ c → DC.lim′ (fobj F′ c) .arr j
        ; natural = λ {c} {d} {f} → D.≈.trans
            (arr∘trans (fmap F′ f) (DC.lim′ (fobj F′ c)) (DC.lim′ (fobj F′ d)) j)
            (D.∘-resp-l F′fj≈Fjf)
        }
      ; commute = λ {i} {j} f → ≈-intro λ {c} → D.≈.trans
          (DC.lim′ (fobj F′ c) .commute f)
          (D.∘-resp-l F′cf≈Ffc)
      }
    ; isLimit = λ X → record
      { arr = record
        { arr = record
          { component = λ c → !! (DC.lim′ (F′ .fobj c)) (apCone X c)
          ; natural = λ {c} {d} {f} →
            begin
              !! (DC.lim′ (fobj F′ d)) (apCone X d) D.∘ fmap (Apex X) f
            ≈⟨ !!∘ (DC.lim′ (fobj F′ d)) {C = record
                  { Apex = Apex X .fobj c
                  ; arr = λ j → apCone X d .arr j D.∘ Apex X .fmap f
                  ; commute = λ {i} {j} g → D.≈.sym (
                    begin
                      (F .fobj j .fmap C.id D.∘ F .fmap g .component d) D.∘
                        X .arr i .component d D.∘ Apex X .fmap f
                    ≈⟨ D.∘-resp-l
                        (D.≈.trans (D.∘-resp-l (F .fobj j .fmap-id)) D.id-l) ⟩
                      F .fmap g .component d D.∘ X .arr i .component d D.∘
                        Apex X .fmap f
                    ≈⟨ D.unassoc ⟩
                      (F .fmap g .component d D.∘ X .arr i .component d) D.∘
                        Apex X .fmap f
                    ≈⟨ D.∘-resp-l (D.≈.sym (X .commute g .≈-elim)) ⟩
                      X .arr j .component d D.∘ Apex X .fmap f
                    ∎)
                  }} record
                    { commute = λ j → D.≈.refl } ⟩
              !! (DC.lim′ (fobj F′ d)) _
            ≈⟨ !!-unique (DC.lim′ (fobj F′ d)) record
                  { commute = λ j →
                    begin
                      DC.lim′ (fobj F′ d) .arr j D.∘
                      trans (F′ .fmap f) (DC.lim′ (fobj F′ c)) (DC.lim′ (fobj F′ d)) D.∘
                      !! (DC.lim′ (fobj F′ c)) (apCone X c)
                    ≈⟨ D.unassoc ⟩
                      (DC.lim′ (fobj F′ d) .arr j D.∘
                      trans (F′ .fmap f) (DC.lim′ (fobj F′ c)) (DC.lim′ (fobj F′ d))) D.∘
                      !! (DC.lim′ (fobj F′ c)) (apCone X c)
                    ≈⟨ D.∘-resp-l
                          (arr∘trans (F′ .fmap f) (DC.lim′ (fobj F′ c))
                            (DC.lim′ (fobj F′ d)) j) ⟩
                      (F′ .fmap f .component j D.∘ DC.lim′ (fobj F′ c) .arr j) D.∘
                      !! (DC.lim′ (fobj F′ c)) (apCone X c)
                    ≈⟨ D.assoc ⟩
                      F′ .fmap f .component j D.∘
                      DC.lim′ (fobj F′ c) .arr j D.∘
                      !! (DC.lim′ (fobj F′ c)) (apCone X c)
                    ≈⟨ D.∘-resp-r (arr∘!! (DC.lim′ (fobj F′ c)) (apCone X c)) ⟩
                      F′ .fmap f .component j D.∘ X .arr j .component c
                    ≈⟨ D.∘-resp-l F′fj≈Fjf ⟩
                      F .fobj j .fmap f D.∘ X .arr j .component c
                    ≈˘⟨ X .arr j .natural  ⟩
                      X .arr j .component d D.∘ Apex X .fmap f
                    ∎
                  } ⟩
              fmap (DC.limF ∘ F′) f D.∘ !! (DC.lim′ (fobj F′ c)) (apCone X c)
            ∎
          }
        ; commute = λ j → ≈-intro λ {c} → arr∘!! (DC.lim′ (F′ .fobj c)) (apCone X c)
        }
      ; unique = λ {g} _ → ≈-intro λ {c} → !!-unique (DC.lim′ (F′ .fobj c)) record
          { commute = λ j → g .commute j .≈-elim
          }
      }
    }
    where
      module C = Category C
      module D = Category D
      module J = Category J
      open D.≈-Reasoning
      module DC = Complete D-complete


      F′ : Functor C (J ↝ D)
      F′ = Curry (Uncurry F ∘ Swap)


      F′fj≈Fjf : ∀ {c d} {f : c C.⇒ d} {j}
        → F′ .fmap f .component j D.≈ F .fobj j .fmap f
      F′fj≈Fjf = D.≈.trans (D.∘-resp-r (fmap-id F .≈-elim)) D.id-r


      F′cf≈Ffc : ∀ {c i j} {f : i J.⇒ j}
        → F′ .fobj c .fmap f D.≈ F .fmap f .component c
      F′cf≈Ffc = D.≈.trans (D.∘-resp-l (fmap-id (fobj F _))) D.id-l


      apCone : Cone F → ∀ c → Cone (fobj F′ c)
      apCone X c = record
        { Apex = Apex X .fobj c
        ; arr = λ j → X .arr j .component c
        ; commute = λ f → D.≈.trans
            (X .commute f .≈-elim)
            (D.∘-resp-l (D.≈.sym F′cf≈Ffc))
        }
