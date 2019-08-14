module Cats.Limit where

open import Level

open import Cats.Category.Base
open import Cats.Category.Cones as Cones using
  (Cone ; Cones ; ConesF ; cone-iso→obj-iso)
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
  IsLimit {D} = Terminal.IsTerminal (Cones D)


  record Limit (D : Functor J Z) : Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′) where
    field
      cone : Cone D
      isLimit : IsLimit cone

    ! : ∀ (cone′ : Cone D) → cone′ Cs.⇒ cone
    ! cone′ = isLimit cone′ .∃!′.arr


    !! : ∀ (cone′ : Cone D) → Apex cone′ Z.⇒ Apex cone
    !! cone′ = (! cone′) .arr


    !-unique : ∀ {cone′ : Cone D} (f : cone′ Cs.⇒ cone)
      → ! cone′ Cs.≈ f
    !-unique {cone′} f = isLimit cone′ .∃!′.unique {f} _


    !!-unique : ∀ {cone′ : Cone D} (f : cone′ Cs.⇒ cone)
      → !! cone′ Z.≈ f .arr
    !!-unique f = !-unique f


    open Cone cone public


  open Limit public


  instance
    HasObj-Limit : ∀ {D} → HasObj (Limit D) _ _ _
    HasObj-Limit {D} = record { Cat = Cones D ; _ᴼ = cone }


  module _ {D : Functor J Z} where

    unique : (l m : Limit D) → Iso.Build._≅_ (Cones D) (l ᴼ) (m ᴼ)
    unique l m = Terminal.terminal-unique (Cones D) (isLimit l) (isLimit m)


    obj-unique : (l m : Limit D) → Iso.Build._≅_ Z (l ᴼ ᴼ) (m ᴼ ᴼ)
    obj-unique l m = cone-iso→obj-iso _ (unique l m)


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
    ; fmap = λ {F} {G} ϑ → !! (lim′ _) (ConesF .fmap ϑ .fobj (lim′ _ .cone))
    ; fmap-resp = λ {F} {G} {ϑ} {ι} ϑ≈ι → !!-unique (lim′ _) record
      { commute = λ j → C.≈.trans
          (commute (! (lim′ G) (ConesF .fmap ι .fobj (cone (lim′ F)))) j)
          (C.∘-resp-l (C.≈.sym (≈-elim ϑ≈ι)))
      }
    ; fmap-id = !!-unique (lim′ _) record
        { commute = λ j → C.≈.trans C.id-r (C.≈.sym C.id-l)
        }
    ; fmap-∘ = λ {F} {G} {H} {ϑ} {ι} → C.≈.sym (!!-unique (lim′ _) record
        { commute = λ j → let open C.≈-Reasoning in
          begin
            lim′ H .cone .arr j C.∘
            !! (lim′ H) (ConesF .fmap ϑ .fobj (lim′ G .cone)) C.∘
            !! (lim′ G) (ConesF .fmap ι .fobj (lim′ F .cone))
          ≈⟨ C.unassoc ⟩
            (lim′ H .cone .arr j C.∘
            !! (lim′ H) (ConesF .fmap ϑ .fobj (lim′ G .cone))) C.∘
            !! (lim′ G) (ConesF .fmap ι .fobj (lim′ F .cone))
          ≈⟨ C.∘-resp-l
              (commute (! (lim′ H) (ConesF .fmap ϑ .fobj (lim′ G .cone))) j) ⟩
            ConesF .fmap ϑ .fobj (lim′ G .cone) .arr j C.∘
            !! (lim′ G) (ConesF .fmap ι .fobj (lim′ F .cone))
          ≡⟨⟩
            (component ϑ j C.∘ lim′ G .cone .arr j) C.∘
            !! (lim′ G) (ConesF .fmap ι .fobj (lim′ F .cone))
          ≈⟨ C.assoc ⟩
            component ϑ j C.∘ lim′ G .cone .arr j C.∘
            !! (lim′ G) (ConesF .fmap ι .fobj (lim′ F .cone))
          ≈⟨ C.∘-resp-r (commute (! (lim′ G) (ConesF .fmap ι .fobj (lim′ F .cone))) j) ⟩
            component ϑ j C.∘ ConesF .fmap ι .fobj (lim′ F .cone) .arr j
          ≡⟨⟩
            component ϑ j C.∘ (component ι j C.∘ lim′ F .cone .arr j)
          ≈⟨ C.unassoc ⟩
            component (ϑ J↝C.∘ ι) j C.∘ lim′ F .cone .arr j
          ∎
        })
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
