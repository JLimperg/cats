module Cats.Category.Cones where

open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Level using (_⊔_)

open import Cats.Category.Base
open import Cats.Category.Cat using (Cat)
open import Cats.Category.Fun as Fun using (Fun ; Trans)
open import Cats.Functor using (Functor) renaming (_∘_ to _∘F_)
open import Cats.Util.Conv

import Relation.Binary.PropositionalEquality as ≡

import Cats.Category.Constructions.Iso as Iso
import Cats.Util.Function as Fun

open Functor
open Trans
open Fun._≈_


module Build {lo la l≈ lo′ la′ l≈′}
  {J : Category lo la l≈}
  {Z : Category lo′ la′ l≈′}
  (D : Functor J Z)
  where

  infixr 9 _∘_
  infixr 4 _≈_

  private
    module Z = Category Z
    module J = Category J
    module D = Functor D


  -- We could define cones in terms of wedges (and limits in terms of ends).
  record Cone : Set (lo ⊔ la ⊔ la′ ⊔ lo′ ⊔ l≈′) where
    field
      Apex : Z.Obj
      arr : ∀ j → Apex Z.⇒ D.fobj j
      commute : ∀ {i j} (α : i J.⇒ j) → arr j Z.≈ D.fmap α Z.∘ arr i

  open Cone public


  instance
    HasObj-Cone : HasObj Cone lo′ la′ l≈′
    HasObj-Cone = record { Cat = Z ; _ᴼ = Cone.Apex }


  Obj = Cone


  record _⇒_ (A B : Obj) : Set (lo ⊔ la′ ⊔ l≈′) where
    private
      module A = Cone A ; module B = Cone B

    field
      arr : A.Apex Z.⇒ B.Apex
      commute : ∀ j → B.arr j Z.∘ arr Z.≈ A.arr j


  open _⇒_ public


  instance
    HasArrow-⇒ : ∀ {A B} → HasArrow (A ⇒ B) lo′ la′ l≈′
    HasArrow-⇒ = record { Cat = Z ; _⃗ = _⇒_.arr }


  _≈_ : ∀ {A B} → Rel (A ⇒ B) l≈′
  _≈_ = Z._≈_ Fun.on arr


  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv = Fun.on-isEquivalence _⇒_.arr Z.equiv


  id : ∀ {A} → A ⇒ A
  id = record
      { arr = Z.id
      ; commute = λ j → Z.id-r
      }


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  _∘_ {A} {B} {C} f g = record
      { arr = f ⃗ Z.∘ g ⃗
      ; commute = λ j →
          begin
            arr C j Z.∘ f ⃗ Z.∘ g ⃗
          ≈⟨ Z.unassoc ⟩
            (arr C j Z.∘ f ⃗) Z.∘ g ⃗
          ≈⟨ Z.∘-resp-l (commute f j) ⟩
            arr B j Z.∘ g ⃗
          ≈⟨ commute g j ⟩
            arr A j
          ∎
      }
    where
      open Z.≈-Reasoning


  Cones : Category (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) (lo ⊔ la′ ⊔ l≈′) l≈′
  Cones = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = Z.∘-resp
      ; id-r = Z.id-r
      ; id-l = Z.id-l
      ; assoc = Z.assoc
      }


  open Iso.Build Cones using (_≅_)
  open Iso.Build Z using () renaming (_≅_ to _≅Z_)


  cone-iso→obj-iso : ∀ {c d : Cone}
    → c ≅ d
    → c ᴼ ≅Z d ᴼ
  cone-iso→obj-iso i = record
      { forth = forth i ⃗
      ; back = back i ⃗
      ; back-forth = back-forth i
      ; forth-back = forth-back i
      }
    where
      open _≅_


open Build public hiding (HasObj-Cone ; HasArrow-⇒)

private
  open module Build′ {lo la l≈ lo′ la′ l≈′}
    {J : Category lo la l≈}
    {Z : Category lo′ la′ l≈′}
    {D : Functor J Z}
    = Build D
    public using (HasObj-Cone ; HasArrow-⇒)


-- TODO better name
apFunctor : ∀ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  → {Y : Category lo la l≈}
  → {Z : Category lo′ la′ l≈′}
  → (F : Functor Y Z)
  → {J : Category lo″ la″ l≈″}
  → {D : Functor J Y}
  → Cone D
  → Cone (F ∘F D)
apFunctor {Y = Y} {Z} F {J} {D} c = record
    { Apex = fobj F (c .Apex)
    ; arr = λ j → fmap F (c .arr j)
    ; commute = λ {i} {j} α → Z.≈.sym (
        begin
          fmap F (fmap D α) Z.∘ fmap F (c .arr i)
        ≈⟨ fmap-∘ F ⟩
          fmap F (fmap D α Y.∘ c .arr i)
        ≈⟨ fmap-resp F (Y.≈.sym (c .commute α)) ⟩
          fmap F (c .arr j)
        ∎
      )
    }
  where
    module Y = Category Y
    module Z = Category Z
    open Z.≈-Reasoning


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  module D = Category D


  trans : {F G : Functor C D} → Trans F G → Cone F → Cone G
  trans {F} {G} θ c = record
    { Apex = c .Apex
    ; arr = λ j → component θ j D.∘ c .arr j
    ; commute = λ {i} {j} α →
      let open D.≈-Reasoning in
      begin
      component θ j D.∘ c .arr j
      ≈⟨ D.∘-resp-r (c .commute α) ⟩
      component θ j D.∘ fmap F α D.∘ c .arr i
      ≈⟨ D.unassoc ⟩
      (component θ j D.∘ fmap F α) D.∘ c .arr i
      ≈⟨ D.∘-resp-l (natural θ) ⟩
      (fmap G α D.∘ component θ i) D.∘ c .arr i
      ≈⟨ D.assoc ⟩
      fmap G α D.∘ component θ i D.∘ c .arr i
      ∎
    }


  ConesF : Functor (Fun C D) (Cat (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) (lo ⊔ la′ ⊔ l≈′) l≈′)
  ConesF = record
    { fobj = Cones
    ; fmap = λ {F} {G} ϑ → record
      { fobj = λ c → trans ϑ c
      ; fmap = λ f → record
        { arr = f .arr
        ; commute = λ j → D.≈.trans D.assoc (D.∘-resp-r (commute f j))
        }
      ; fmap-resp = λ x → x
      ; fmap-id = D.≈.refl
      ; fmap-∘ = D.≈.refl
      }
    ; fmap-resp = λ ϑ≈ι → record
      { iso = record
        { forth = record
          { arr = D.id
          ; commute = λ j → D.≈.trans D.id-r (D.∘-resp-l (D.≈.sym (≈-elim ϑ≈ι)))
          }
        ; back = record
          { arr = D.id
          ; commute = λ j → D.≈.trans D.id-r (D.∘-resp-l (≈-elim ϑ≈ι))
          }
        ; back-forth = D.id-l
        ; forth-back = D.id-l
        }
      ; forth-natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
      }
    ; fmap-id = record
      { iso = record
        { forth = record
          { arr = D.id
          ; commute = λ j → D.≈.trans D.id-r (D.≈.sym D.id-l)
          }
        ; back = record
          { arr = D.id
          ; commute = λ j → D.≈.trans D.id-r D.id-l
          }
        ; back-forth = D.id-l
        ; forth-back = D.id-l
        }
      ; forth-natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
      }
    ; fmap-∘ = record
      { iso = record
        { forth = record
          { arr = D.id
          ; commute = λ j → D.≈.trans D.id-r D.assoc
          }
        ; back = record
          { arr = D.id
          ; commute = λ j → D.≈.trans D.id-r D.unassoc
          }
        ; back-forth = D.id-l
        ; forth-back = D.id-l
        }
      ; forth-natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
      }
    }
