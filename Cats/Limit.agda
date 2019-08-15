module Cats.Limit where

open import Level

open import Cats.Category.Base
open import Cats.Category.Cones as Cones using
  (Cone ; Cones ; ConesF ; cone-iso→obj-iso)
open import Cats.Category.Constructions.Terminal using (HasTerminal)
open import Cats.Category.Constructions.Unique using (∃!′)
open import Cats.Category.Fun as Fun using (Trans ; _↝_)
open import Cats.Functor using (Functor)
open import Cats.Util.Conv

import Cats.Category.Constructions.Terminal as Terminal
import Cats.Category.Constructions.Iso as Iso

open Cone
open Cones._⇒_
open Functor
open Fun._≈_
open Trans


private
  module Cs {lo la l≈ lo′ la′ l≈′} {C : Category lo la l≈}
    {D : Category lo′ la′ l≈′} {F : Functor C D} = Category (Cones F)


module _ {lo la l≈ lo′ la′ l≈′}
  {J : Category lo la l≈}
  {Z : Category lo′ la′ l≈′}
  where

  private
    module J = Category J
    module Z = Category Z


  IsLimit : {D : Functor J Z} → Cone D → Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′)
  IsLimit {D} = Terminal.IsTerminal {C = Cones D}


  record Limit (D : Functor J Z) : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) where
    field
      cone : Cone D
      isLimit : IsLimit cone


    open Cone cone using () renaming (arr to proj)


    private
      hasTerminal : HasTerminal (Cones D)
      hasTerminal = record { ⊤ = cone ; isTerminal = isLimit }


    open HasTerminal hasTerminal public using
      ( ! ; !-unique ) renaming
      ( ⊤-unique to cone-unique
      ; ⇒⊤-unique to ⇒cone-unique )


    !! : (cone′ : Cone D) → cone′ .Cone.Apex Z.⇒ cone .Cone.Apex
    !! cone′ = ! cone′ .arr


    !!-unique : {cone′ : Cone D} (f : cone′ Cs.⇒ cone)
      → !! cone′ Z.≈ f .arr
    !!-unique f = !-unique f


    arr∘!! : ∀ cone′ {j} → proj j Z.∘ !! cone′ Z.≈ cone′ .Cone.arr j
    arr∘!! cone′ = ! cone′ .commute _


    !!∘ : ∀ {C D} (f : C Cs.⇒ D)
      → !! D Z.∘ f .arr Z.≈ !! C
    !!∘ {C} {D} f = Z.≈.sym (!!-unique record
      { commute = λ j →
        let open Z.≈-Reasoning in
        begin
          proj j Z.∘ !! D Z.∘ f .arr
        ≈⟨ Z.unassoc ⟩
          (proj j Z.∘ !! D) Z.∘ f .arr
        ≈⟨ Z.∘-resp-l (arr∘!! D) ⟩
          D .arr j Z.∘ f .arr
        ≈⟨ f .commute j ⟩
          C .arr j
        ∎
      })


    open Cone cone public


  open Limit public


  instance
    HasObj-Limit : ∀ {D} → HasObj (Limit D) _ _ _
    HasObj-Limit {D} = record { Cat = Cones D ; _ᴼ = cone }


  module _ {D : Functor J Z} where

    unique : (l m : Limit D) → Iso.Build._≅_ (Cones D) (l ᴼ) (m ᴼ)
    unique l m = Terminal.terminal-unique (isLimit l) (isLimit m)


    obj-unique : (l m : Limit D) → Iso.Build._≅_ Z (l ᴼ ᴼ) (m ᴼ ᴼ)
    obj-unique l m = cone-iso→obj-iso _ (unique l m)


  module _ {F G : Functor J Z} where

    trans : (ϑ : Trans F G) (l : Limit F) (m : Limit G)
      → l .Apex Z.⇒ m .Apex
    trans ϑ l m = !! m (ConesF .fmap ϑ .fobj (l .cone))


    arr∘trans : ∀ ϑ l m c
      →   m .arr c Z.∘ trans ϑ l m
      Z.≈ ϑ .component c Z.∘ l .arr c
    arr∘trans ϑ l m c = arr∘!! m (ConesF .fmap ϑ .fobj (l .cone))


    trans-resp : ∀ {ϑ ι} l m
      → ϑ Fun.≈ ι
      → trans ϑ l m Z.≈ trans ι l m
    trans-resp {ϑ} {ι} l m ϑ≈ι = !!-unique m record
      { commute = λ j → Z.≈.trans (arr∘trans ι l m j)
          (Z.∘-resp-l (Z.≈.sym (≈-elim ϑ≈ι)))
      }

  trans-id : {F : Functor J Z} (l : Limit F)
    → trans Fun.id l l Z.≈ Z.id
  trans-id l = !!-unique l record
    { commute = λ j → Z.≈.trans Z.id-r (Z.≈.sym Z.id-l)
    }


  trans-∘ : {F G H : Functor J Z} (ϑ : Trans G H) (ι : Trans F G)
    → ∀ l m n
    → trans ϑ m n Z.∘ trans ι l m Z.≈ trans (ϑ Fun.∘ ι) l n
  trans-∘ {F} {G} {H} ϑ ι l m n = Z.≈.sym (!!-unique n record
      { commute = λ j → let open Z.≈-Reasoning in
        begin
          n .arr j Z.∘ trans ϑ m n Z.∘ trans ι l m
        ≈⟨ Z.unassoc ⟩
          (n .arr j Z.∘ trans ϑ m n) Z.∘ trans ι l m
        ≈⟨ Z.∘-resp-l (arr∘trans ϑ m n j ) ⟩
          (ϑ .component j Z.∘ m .arr j) Z.∘ trans ι l m
        ≈⟨ Z.assoc ⟩
          ϑ .component j Z.∘ m .arr j Z.∘ trans ι l m
        ≈⟨ Z.∘-resp-r (arr∘trans ι l m j) ⟩
          ϑ .component j Z.∘ ι .component j Z.∘ l .arr j
        ≈⟨ Z.unassoc ⟩
          (ϑ Fun.∘ ι) .component j Z.∘ l .arr j
        ∎
      })


record _HasLimitsOf_
  {lo la l≈} (C : Category lo la l≈) {lo′ la′ l≈′} (J : Category lo′ la′ l≈′)
  : Set (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′ )
  where
  private
    module C = Category C
    module J↝C = Category (J ↝ C)


  field
    lim′ : (F : Functor J C) → Limit F


  lim : Functor J C → C.Obj
  lim F = lim′ F .cone .Apex


  limF : Functor (J ↝ C) C
  limF = record
    { fobj = λ F → lim F
    ; fmap = λ {F} {G} ϑ → trans ϑ (lim′ _) (lim′ _)
    ; fmap-resp = λ ϑ≈ι → trans-resp (lim′ _) (lim′ _) ϑ≈ι
    ; fmap-id = trans-id (lim′ _)
    ; fmap-∘ = trans-∘ _ _ (lim′ _) (lim′ _) (lim′ _)
    }


record Complete {lo la l≈} (C : Category lo la l≈) lo′ la′ l≈′
  : Set (lo ⊔ la ⊔ l≈ ⊔ suc (lo′ ⊔ la′ ⊔ l≈′))
  where
  field
    lim′ : ∀ {J : Category lo′ la′ l≈′} (F : Functor J C) → Limit F


  hasLimitsOf : (J : Category lo′ la′ l≈′) → C HasLimitsOf J
  hasLimitsOf J ._HasLimitsOf_.lim′ = lim′


  private
    open module HasLimitsOf {J} = _HasLimitsOf_ (hasLimitsOf J) public hiding (lim′)



preservesLimits : ∀ {lo la l≈ lo′ la′ l≈′}
  → {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  → Functor C D
  → (lo″ la″ l≈″ : Level)
  → Set _
preservesLimits {C = C} F lo″ la″ l≈″
    = {J : Category lo″ la″ l≈″}
    → {D : Functor J C}
    → {c : Cone D}
    → IsLimit c
    → IsLimit (Cones.apFunctor F c)
