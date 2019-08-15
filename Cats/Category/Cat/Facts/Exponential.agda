module Cats.Category.Cat.Facts.Exponential where

open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)

open import Cats.Bifunctor using
  (Bifunctor ; Bifunctor→Functor₁ ; transposeBifunctor₁ ; transposeBifunctor₁-resp)
open import Cats.Category
open import Cats.Category.Cat as Cat′ using
  (Cat ; Functor ; _∘_ ; _≈_) renaming
  (id to Id)
open import Cats.Category.Cat.Facts.Product using (hasBinaryProducts ; ⟨_×_⟩)
open import Cats.Category.Fun using (_↝_ ; Trans ; ≈-intro ; ≈-elim)
open import Cats.Category.Fun.Facts.Iso using (≈→≅)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Trans.Iso as NatIso using (NatIso)
open import Cats.Util.Conv
open import Cats.Util.Simp using (simp!)

import Cats.Category.Base as Base
import Cats.Category.Constructions.Unique as Unique
import Cats.Category.Constructions.Iso as Iso

open Functor
open Trans
open Iso.Iso


private
  module Cat≈ {lo la l≈ lo′ la′ l≈′}
    {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
    = IsEquivalence (Cat′.equiv {C = C} {D})


  module Fun {lo la l≈ lo′ la′ l≈′}
    {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
    = Category (C ↝ D)


module _ {lo la l≈ lo′ la′ l≈′}
  {B : Category lo la l≈} {C : Category lo′ la′ l≈′}
  where

  private
    module B = Category B
    module C = Category C


  Eval : Bifunctor (B ↝ C) B C
  Eval = record
      { fobj = λ where
          (F , x) → fobj F x
      ; fmap = λ where
          {F , a} {G , b} (θ , f) → fmap G f C.∘ component θ a
      ; fmap-resp = λ where
          {F , a} {G , b} {θ , f} {ι , g} (θ≈ι , f≈g) →
            C.∘-resp (fmap-resp G f≈g) (≈-elim θ≈ι)
      ; fmap-id = λ { {F , b} → C.≈.trans (C.∘-resp-l (fmap-id F)) C.id-l }
      ; fmap-∘ = λ where
          {F , a} {G , b} {H , c} {θ , f} {ι , g} →
            begin
              (fmap H f C.∘ component θ b) C.∘ (fmap G g C.∘ component ι a)
            ≈⟨ C.∘-resp-l (C.≈.sym (natural θ)) ⟩
              (component θ c C.∘ fmap G f) C.∘ (fmap G g C.∘ component ι a)
            ≈⟨ simp! C ⟩
              component θ c C.∘ (fmap G f C.∘ fmap G g) C.∘ component ι a
            ≈⟨ C.∘-resp-r (C.∘-resp-l (fmap-∘ G)) ⟩
              component θ c C.∘ fmap G (f B.∘ g) C.∘ component ι a
            ≈⟨ C.unassoc ⟩
              (component θ c C.∘ fmap G (f B.∘ g)) C.∘ component ι a
            ≈⟨ C.∘-resp-l (natural θ) ⟩
              (fmap H (f B.∘ g) C.∘ component θ a) C.∘ component ι a
            ≈⟨ C.assoc ⟩
              fmap H (f B.∘ g) C.∘ component θ a C.∘ component ι a
            ∎
      }
    where
      open C.≈-Reasoning


module _ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  {B : Category lo la l≈} {C : Category lo′ la′ l≈′} {D : Category lo″ la″ l≈″}
  where

  private
    module B = Category B
    module C = Category C
    module D = Category D


  Curry : Bifunctor B C D → Functor B (C ↝ D)
  Curry F = transposeBifunctor₁ F


  Curry-resp : ∀ {F G} → F ≈ G → Curry F ≈ Curry G
  Curry-resp = transposeBifunctor₁-resp


  Curry-correct : ∀ {F} → Eval ∘ ⟨ Curry F × Id ⟩ ≈ F
  Curry-correct {F} = record
      { iso = D.≅.refl
      ; forth-natural = λ where
        {a , a′} {b , b′} {f , f′} →
          begin
            D.id D.∘ fmap F (B.id , f′) D.∘ fmap F (f , C.id)
          ≈⟨ D.≈.trans D.id-l (fmap-∘ F) ⟩
            fmap F (B.id B.∘ f , f′ C.∘ C.id)
          ≈⟨ fmap-resp F (B.id-l , C.id-r) ⟩
            fmap F (f , f′)
          ≈⟨ D.≈.sym D.id-r ⟩
            fmap F (f , f′) D.∘ D.id
          ∎
      }
    where
      open D.≈-Reasoning


  Curry-unique : ∀ {F Curry′}
    → Eval ∘ ⟨ Curry′ × Id ⟩ ≈ F
    → Curry′ ≈ Curry F
  Curry-unique {F} {Curry′} eq@record { iso = iso ; forth-natural = fnat } = record
      { iso = λ {x} →
          let open Fun.≅-Reasoning in
          Fun.≅.sym (
            begin
              fobj (Curry F) x
            ≈⟨ NatIso.iso (Curry-resp (Cat≈.sym eq)) ⟩
              fobj (Curry (Eval ∘ ⟨ Curry′ × Id ⟩)) x
            ≈⟨ ≈→≅ (lem x) ⟩
              fobj Curry′ x
            ∎
          )
      ; forth-natural = λ {a} {b} {f} → ≈-intro λ {x} →
          -- TODO We need a simplification tactic.
          let open D.≈-Reasoning in
          triangle (forth iso D.∘ component (fmap Curry′ f) x)
          ( begin
              ((forth iso D.∘
                 (fmap (fobj Curry′ b) C.id D.∘ component (fmap Curry′ B.id) x) D.∘ D.id) D.∘
               D.id D.∘ D.id) D.∘
              component (fmap Curry′ f) x
            ≈⟨ D.∘-resp-l (D.≈.trans (D.∘-resp-r D.id-l) (D.≈.trans D.id-r
                (D.≈.trans (D.∘-resp-r (D.≈.trans D.id-r (D.≈.trans
                  (D.∘-resp (fmap-id (fobj Curry′ b))
                    (≈-elim (fmap-id Curry′))) D.id-l))) D.id-r))) ⟩
              forth iso D.∘ component (fmap Curry′ f) x
            ∎
          )
          ( begin
              fmap F (f , C.id) D.∘
              (forth iso D.∘ (fmap (fobj Curry′ a) C.id D.∘ component (fmap Curry′ B.id) x) D.∘ D.id) D.∘
              D.id D.∘ D.id
            ≈⟨ D.∘-resp-r (D.≈.trans (D.∘-resp-r D.id-r) (D.≈.trans D.id-r
                (D.≈.trans (D.∘-resp-r (D.≈.trans D.id-r (D.≈.trans
                  (D.∘-resp-l (fmap-id (fobj Curry′ a)))
                    (D.≈.trans D.id-l (≈-elim (fmap-id Curry′)))))) D.id-r))) ⟩
              fmap F (f , C.id) D.∘ forth iso
            ≈⟨ D.≈.sym fnat ⟩
              forth iso D.∘ fmap (fobj Curry′ b) C.id D.∘ component (fmap Curry′ f) x
            ≈⟨ D.∘-resp-r (D.≈.trans (D.∘-resp-l (fmap-id (fobj Curry′ b))) D.id-l) ⟩
              forth iso D.∘ component (fmap Curry′ f) x
            ∎
          )
      }
    where
      lem : ∀ x
        → NatIso (Bifunctor→Functor₁ (Eval ∘ ⟨ Curry′ × Id ⟩) x) (fobj Curry′ x)
      lem x = record
          { iso = D.≅.refl
          ; forth-natural = D.≈.trans D.id-l (D.∘-resp-r (≈-elim (fmap-id Curry′)))
          }


  -- We get the following lemmas for free from HasExponentials, but only when
  -- all the categories are at the same (single) level.

  Uncurry : Functor B (C ↝ D) → Bifunctor B C D
  Uncurry F = Eval ∘ ⟨ F × Id ⟩


  Curry∘Uncurry : {F : Functor B (C ↝ D)}
    → Curry (Uncurry F) ≈ F
  Curry∘Uncurry {F} = Cat≈.sym (Curry-unique {Curry′ = F} Cat≈.refl)


  Uncurry∘Curry : {F : Bifunctor B C D}
    → Uncurry (Curry F) ≈ F
  Uncurry∘Curry {F} = Curry-correct {F = F}


instance
  hasExponentials : ∀ {l} → HasExponentials (Cat l l l)
  hasExponentials {l} = record
      { _↝′_ = λ B C → record
          { Cᴮ = B ↝ C
          ; eval = Eval
          ; curry′ = λ F → record
              { arr = Curry F
              ; prop = Curry-correct {F = F}
              ; unique = λ {g} eq → Cat≈.sym (Curry-unique eq)
              }
          }
      }
