module Cats.Category.Arrow where

open import Level
open import Relation.Binary using (IsEquivalence ; _Preserves₂_⟶_⟶_)

open import Cats.Category


module _ {lo la l≈} (C : Category lo la l≈) where

  infixr 9 _∘_
  infixr 4 _≈_

  private
    module C = Category C
    module ≈ = C.≈


  record Obj : Set (lo ⊔ la) where
    field
      Dom : C.Obj
      Cod : C.Obj
      arr : Dom C.⇒ Cod

  open Obj


  record _⇒_ (f g : Obj) : Set (la ⊔ l≈) where
    field
      dom : Dom f C.⇒ Dom g
      cod : Cod f C.⇒ Cod g
      commute : arr g C.∘ dom C.≈ cod C.∘ arr f

  open _⇒_


  record _≈_ {A B} (F G : A ⇒ B) : Set l≈ where
    field
      dom : dom F C.≈ dom G
      cod : cod F C.≈ cod G


  id : ∀ {A} → A ⇒ A
  id {record { Dom = Dom ; Cod = Cod ; arr = arr }}
      = record
      { dom = C.id
      ; cod = C.id
      ; commute = ≈.trans C.id-r (≈.sym C.id-l)
      }


  _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
  _∘_ {F} {G} {H}
    record { dom = F-dom ; cod = F-cod ; commute = F-commute }
    record { dom = G-dom ; cod = G-cod ; commute = G-commute }
      = record
      { dom = F-dom C.∘ G-dom
      ; cod = F-cod C.∘ G-cod
      ; commute
          = begin
              arr H C.∘ F-dom C.∘ G-dom
            ≈⟨ ≈.sym C.assoc ⟩
              (arr H C.∘ F-dom) C.∘ G-dom
            ≈⟨ C.∘-resp F-commute ≈.refl ⟩
              (F-cod C.∘ arr G) C.∘ G-dom
            ≈⟨ C.assoc ⟩
              F-cod C.∘ arr G C.∘ G-dom
            ≈⟨ C.∘-resp ≈.refl G-commute ⟩
              F-cod C.∘ G-cod C.∘ arr F
            ≈⟨ ≈.sym C.assoc ⟩
              (F-cod C.∘ G-cod) C.∘ arr F
            ∎
      }
    where
      open C.≈-Reasoning


  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv = record
      { refl = record { dom = ≈.refl ; cod = ≈.refl }
      ; sym = λ where
          record { dom = dom ; cod = cod } → record
            { dom = ≈.sym dom
            ; cod = ≈.sym cod
            }
      ; trans = λ where
          record { dom = dom₁ ; cod = cod₁ } record { dom = dom₂ ; cod = cod₂ }
            → record
            { dom = ≈.trans dom₁ dom₂
            ; cod = ≈.trans cod₁ cod₂
            }
      }


  ∘-resp : ∀ {A B C} → (_∘_ {A} {B} {C}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ∘-resp
    record { dom = dom-FG ; cod = cod-FG }
    record { dom = dom-HI ; cod = cod-HI }
      = record
      { dom = C.∘-resp dom-FG dom-HI
      ; cod = C.∘-resp cod-FG cod-HI
      }


  id-r : ∀ {A B} {F : A ⇒ B} → F ∘ id ≈ F
  id-r = record
      { dom = C.id-r
      ; cod = C.id-r
      }


  id-l : ∀ {A B} {F : A ⇒ B} → id ∘ F ≈ F
  id-l = record
      { dom = C.id-l
      ; cod = C.id-l
      }


  assoc : ∀ {A B C D} {F : C ⇒ D} {G : B ⇒ C} {H : A ⇒ B}
    → (F ∘ G) ∘ H ≈ F ∘ (G ∘ H)
  assoc = record
      { dom = C.assoc
      ; cod = C.assoc
      }


  _⃗ : Category (la ⊔ lo) (l≈ ⊔ la) l≈
  _⃗ = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; equiv = equiv
      ; ∘-resp = ∘-resp
      ; id-r = id-r
      ; id-l = id-l
      ; assoc = assoc
      }
