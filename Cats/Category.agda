module Cats.Category where

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; Σ-syntax)
open import Level
open import Relation.Binary using
  (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_ ; Setoid)

import Relation.Binary.EqReasoning as EqReasoning


record Category lo la l≈ : Set (suc (lo ⊔ la ⊔ l≈)) where
  infixr  9 _∘_
  infix   4 _≈_
  infixr 90 _⇒_

  field
    Obj : Set lo
    _⇒_ : Obj → Obj → Set la
    _≈_ : ∀ {A B} → Rel (A ⇒ B) l≈
    id : {O : Obj} → O ⇒ O
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    ∘-resp : ∀ {A B C} → (_∘_ {A} {B} {C}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    id-r : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    id-l : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    assoc : ∀ {A B C D} (f : C ⇒ D) (g : B ⇒ C) (h : A ⇒ B)
      → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)

  _∘ʳ_ : ∀ {A B C} → A ⇒ B → B ⇒ C → A ⇒ C
  f ∘ʳ g = g ∘ f


  ≈-Setoid : (A B : Obj) → Setoid la l≈
  ≈-Setoid A B = record
      { Carrier = A ⇒ B
      ; _≈_ = _≈_
      ; isEquivalence = equiv
      }


  module ≈ {A B} = IsEquivalence (equiv {A} {B})
  module ≈-Reasoning {A B} = EqReasoning (≈-Setoid A B)


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
      open ≈-Reasoning

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


module _ {lo la l≈} {{C : Category lo la l≈}} where

  open Category C


  IsMono : ∀ {A B} → A ⇒ B → Set (lo ⊔ la ⊔ l≈)
  IsMono {A} f = ∀ {C} {g h : C ⇒ A} → f ∘ g ≈ f ∘ h → g ≈ h


  IsEpi : ∀ {A B} → A ⇒ B → Set (lo ⊔ la ⊔ l≈)
  IsEpi {A} {B} f = ∀ {C} {g h : B ⇒ C} → g ∘ f ≈ h ∘ f → g ≈ h


  IsUnique : ∀ {A B} → A ⇒ B → Set _
  IsUnique {A} {B} f = ∀ (f′ : A ⇒ B) → f ≈ f′


  IsInitial : Obj → Set (lo ⊔ la ⊔ l≈)
  IsInitial Zero = ∀ X → Σ[ f ∈ Zero ⇒ X ] (IsUnique f)


  IsTerminal : Obj → Set (lo ⊔ la ⊔ l≈)
  IsTerminal One = ∀ X → Σ[ f ∈ X ⇒ One ] (IsUnique f)
