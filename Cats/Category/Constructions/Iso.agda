module Cats.Category.Constructions.Iso where

open import Relation.Binary using (IsEquivalence ; Setoid)
open import Level

open import Cats.Category.Base
open import Cats.Util.Conv

import Relation.Binary.EqReasoning as EqReasoning

import Cats.Category.Constructions.Epi as Epi
import Cats.Category.Constructions.Mono as Mono


module Build {lo la l≈} (Cat : Category lo la l≈) where

  private open module Cat = Category Cat
  open Cat.≈-Reasoning
  open Epi.Build Cat
  open Mono.Build Cat


  record _≅_ (A B : Obj) : Set (lo ⊔ la ⊔ l≈) where
    field
      forth : A ⇒ B
      back : B ⇒ A
      back-forth : back ∘ forth ≈ id
      forth-back : forth ∘ back ≈ id

  open _≅_


  instance
    HasArrow-≅ : ∀ {A B} → HasArrow (A ≅ B) lo la l≈
    HasArrow-≅ = record { Cat = Cat ; _⃗ = forth }


  ≅-equiv : IsEquivalence _≅_
  ≅-equiv = record { refl = refl ; sym = sym ; trans = trans }
    where
      refl : ∀ {A} → A ≅ A
      refl {A} = record
          { forth = id
          ; back = id
          ; back-forth = id-l
          ; forth-back = id-l
          }

      sym : ∀ {A B} → A ≅ B → B ≅ A
      sym iso = record
          { forth = back iso
          ; back = forth iso
          ; back-forth = forth-back iso
          ; forth-back = back-forth iso
          }

      trans : ∀ {A B C : Obj} → A ≅ B → B ≅ C → A ≅ C
      trans {A} {B} {C} A≅B B≅C = record
          { forth = forth B≅C ∘ forth A≅B
          ; back = back A≅B ∘ back B≅C
          ; back-forth
              = begin
                  (back A≅B ∘ back B≅C) ∘ forth B≅C ∘ forth A≅B
                ≈⟨ assoc ⟩
                  back A≅B ∘ back B≅C ∘ forth B≅C ∘ forth A≅B
                ≈⟨ ∘-resp-r (≈.trans unassoc (∘-resp-l (back-forth B≅C))) ⟩
                  back A≅B ∘ id ∘ forth A≅B
                ≈⟨ ∘-resp-r id-l ⟩
                  back A≅B ∘ forth A≅B
                ≈⟨ back-forth A≅B ⟩
                  id
                ∎
          ; forth-back
              = begin
                  (forth B≅C ∘ forth A≅B) ∘ back A≅B ∘ back B≅C
                ≈⟨ assoc ⟩
                  forth B≅C ∘ forth A≅B ∘ back A≅B ∘ back B≅C
                ≈⟨ ∘-resp-r (≈.trans unassoc (∘-resp-l (forth-back A≅B))) ⟩
                  forth B≅C ∘ id ∘ back B≅C
                ≈⟨ ∘-resp-r id-l ⟩
                  forth B≅C ∘ back B≅C
                ≈⟨ forth-back B≅C ⟩
                  id
                ∎
          }


  ≅-Setoid : Setoid lo (lo ⊔ la ⊔ l≈)
  ≅-Setoid = record
      { Carrier = Obj
      ; _≈_ = _≅_
      ; isEquivalence = ≅-equiv
      }


  module ≅ = IsEquivalence ≅-equiv
  module ≅-Reasoning = EqReasoning ≅-Setoid


  iso-mono : ∀ {A B} (iso : A ≅ B) → IsMono (forth iso)
  iso-mono iso {g = g} {h} iso∘g≈iso∘h
      = begin
          g
        ≈⟨ ≈.sym id-l ⟩
          id ∘ g
        ≈⟨ ∘-resp-l (≈.sym (back-forth iso)) ⟩
          (back iso ∘ forth iso) ∘ g
        ≈⟨ assoc ⟩
          back iso ∘ forth iso ∘ g
        ≈⟨ ∘-resp-r iso∘g≈iso∘h ⟩
          back iso ∘ forth iso ∘ h
        ≈⟨ unassoc ⟩
          (back iso ∘ forth iso) ∘ h
        ≈⟨ ∘-resp-l (back-forth iso) ⟩
          id ∘ h
        ≈⟨ id-l ⟩
          h
        ∎


  iso-epi : ∀ {A B} (iso : A ≅ B) → IsEpi (forth iso)
  iso-epi iso {g = g} {h} g∘iso≈h∘iso
      = begin
          g
        ≈⟨ ≈.sym id-r ⟩
          g ∘ id
        ≈⟨ ∘-resp-r (≈.sym (forth-back iso)) ⟩
          g ∘ forth iso ∘ back iso
        ≈⟨ unassoc ⟩
          (g ∘ forth iso) ∘ back iso
        ≈⟨ ∘-resp-l g∘iso≈h∘iso ⟩
          (h ∘ forth iso) ∘ back iso
        ≈⟨ assoc ⟩
          h ∘ forth iso ∘ back iso
        ≈⟨ ∘-resp-r (forth-back iso) ⟩
          h ∘ id
        ≈⟨ id-r ⟩
          h
        ∎


open Build public renaming (_≅_ to Iso)
