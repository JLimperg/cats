module Cats.Category.Constructions.Iso where

open import Relation.Binary using (IsEquivalence ; Setoid)
open import Level

open import Cats.Category.Base

import Relation.Binary.EqReasoning as EqReasoning


module Build {lo la l≈} (Cat : Category lo la l≈) where

  private open module Cat = Category Cat
  open Cat.≈-Reasoning


  record _≅_ (A B : Obj) : Set (lo ⊔ la ⊔ l≈) where
    field
      forth : A ⇒ B
      back : B ⇒ A
      back-forth : back ∘ forth ≈ id
      forth-back : forth ∘ back ≈ id

  open _≅_


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
                ≈⟨ assoc (back A≅B) (back B≅C) (forth B≅C ∘ forth A≅B) ⟩
                  back A≅B ∘ back B≅C ∘ forth B≅C ∘ forth A≅B
                ≈⟨ ∘-resp ≈.refl (≈.trans (≈.sym (assoc _ _ _)) (∘-resp (back-forth B≅C) ≈.refl)) ⟩
                  back A≅B ∘ id ∘ forth A≅B
                ≈⟨ ∘-resp ≈.refl id-l ⟩
                  back A≅B ∘ forth A≅B
                ≈⟨ back-forth A≅B ⟩
                  id
                ∎
          ; forth-back
              = begin
                  (forth B≅C ∘ forth A≅B) ∘ back A≅B ∘ back B≅C
                ≈⟨ assoc (forth B≅C) (forth A≅B) (back A≅B ∘ back B≅C) ⟩
                  forth B≅C ∘ forth A≅B ∘ back A≅B ∘ back B≅C
                ≈⟨ ∘-resp ≈.refl (≈.trans (≈.sym (assoc _ _ _)) (∘-resp (forth-back A≅B) ≈.refl)) ⟩
                  forth B≅C ∘ id ∘ back B≅C
                ≈⟨ ∘-resp ≈.refl id-l ⟩
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
