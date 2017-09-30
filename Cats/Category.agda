module Cats.Category where

open import Level
open import Relation.Binary using
  (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_ ; Setoid)

open import Cats.Util.Logic.Constructive

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
  open ≈-Reasoning


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


  ∃! : ∀ {lp} {A B} → (A ⇒ B → Set lp) → Set (la ⊔ l≈ ⊔ lp)
  ∃! {A = A} {B} P = Σ[ f ∈ A ⇒ B ] (P f ∧ (∀ {g} → P g → f ≈ g))

  syntax ∃! (λ f → P) = ∃![ f ] P


  IsMono : ∀ {A B} → A ⇒ B → Set (lo ⊔ la ⊔ l≈)
  IsMono {A} f = ∀ {C} {g h : C ⇒ A} → f ∘ g ≈ f ∘ h → g ≈ h


  IsEpi : ∀ {A B} → A ⇒ B → Set (lo ⊔ la ⊔ l≈)
  IsEpi {A} {B} f = ∀ {C} {g h : B ⇒ C} → g ∘ f ≈ h ∘ f → g ≈ h


  IsUnique : ∀ {A B} → A ⇒ B → Set (l≈ ⊔ la)
  IsUnique {A} {B} f = ∀ (f′ : A ⇒ B) → f ≈ f′


  -- Note: f unique and g unique does not, in general, imply g ∘ f unique. There
  -- can be an h : A ⇒ C which is different from g′ ∘ f′ for any f′, g′.
  ∘-unique : ∀ {A B C} {g : B ⇒ C} {f : A ⇒ B}
    → IsUnique g
    → IsUnique f
    → ∀ {g′ : B ⇒ C} {f′ : A ⇒ B}
    → g ∘ f ≈ g′ ∘ f′
  ∘-unique uniq-g uniq-f = ∘-resp (uniq-g _) (uniq-f _)


  IsInitial : Obj → Set (lo ⊔ la ⊔ l≈)
  IsInitial Zero = ∀ X → Σ[ f ∈ Zero ⇒ X ] (IsUnique f)


  initial→id-unique : ∀ {A} → IsInitial A → IsUnique (id {A})
  initial→id-unique {A} init id′ with init A
  ... | id″ , id″-uniq = ≈.trans (≈.sym (id″-uniq _)) (id″-uniq _)


  initial-unique : ∀ {A B} → IsInitial A → IsInitial B → A ≅ B
  initial-unique {A} {B} A-init B-init = record
      { forth = ∧-eliml (A-init B)
      ; back = ∧-eliml (B-init A)
      ; back-forth = ≈.sym (initial→id-unique A-init _)
      ; forth-back = ≈.sym (initial→id-unique B-init _)
      }


  IsTerminal : Obj → Set (lo ⊔ la ⊔ l≈)
  IsTerminal One = ∀ X → Σ[ f ∈ X ⇒ One ] (IsUnique f)


  terminal→id-unique : ∀ {A} → IsTerminal A → IsUnique (id {A})
  terminal→id-unique {A} term id′ with term A
  ... | id″ , id″-uniq = ≈.trans (≈.sym (id″-uniq _)) (id″-uniq _)


  terminal-unique : ∀ {A B} → IsTerminal A → IsTerminal B → A ≅ B
  terminal-unique {A} {B} A-term B-term = record
      { forth = ∧-eliml (B-term A)
      ; back = ∧-eliml (A-term B)
      ; back-forth = ≈.sym (terminal→id-unique A-term _)
      ; forth-back = ≈.sym (terminal→id-unique B-term _)
      }


  record _×_ (A B : Obj) : Set (lo ⊔ la ⊔ l≈) where
    field
      prod : Obj
      projl : prod ⇒ A
      projr : prod ⇒ B
      ump : ∀ {X} (x-l : X ⇒ A) (x-r : X ⇒ B)
        → ∃![ u ] (x-l ≈ projl ∘ u ∧ x-r ≈ projr ∘ u)


    proj-cancel : ∀ {X} {f g : X ⇒ prod}
      → projl ∘ f ≈ projl ∘ g
      → projr ∘ f ≈ projr ∘ g
      → f ≈ g
    proj-cancel {X} {f} {g} eq-l eq-r with ump (projl ∘ g) (projr ∘ g)
    ... | v , _ , v-uniq
        = begin
            f
          ≈⟨ ≈.sym (v-uniq (≈.sym eq-l , ≈.sym eq-r)) ⟩
            v
          ≈⟨ v-uniq (≈.refl , ≈.refl) ⟩
            g
          ∎

  open _×_


  ×-unique : ∀ {A B} (p q : A × B) → prod p ≅ prod q
  ×-unique {A} {B} p q
    with ump q (projl p) (projr p) | ump p (projl q) (projr q)
  ... | u , (u-eq₁ , u-eq₂) , _ | v , (v-eq₁ , v-eq₂) , _ = record
      { forth = u
      ; back = v
      ; back-forth = proj-cancel p (lemma u-eq₁ v-eq₁) (lemma u-eq₂ v-eq₂)
      ; forth-back = proj-cancel q (lemma v-eq₁ u-eq₁) (lemma v-eq₂ u-eq₂)
      }
    where
      lemma : ∀ {P Q A} {p-projl : P ⇒ A} {q-projl : Q ⇒ A} {v u}
        → p-projl ≈ q-projl ∘ u
        → q-projl ≈ p-projl ∘ v
        → p-projl ∘ v ∘ u ≈ p-projl ∘ id
      lemma {p-projl = p-projl} {q-projl} {v} {u} eq-u eq-v
          = begin
              p-projl ∘ v ∘ u
            ≈⟨ ≈.sym (assoc _ _ _) ⟩
              (p-projl ∘ v) ∘ u
            ≈⟨ ∘-resp (≈.sym eq-v) ≈.refl ⟩
              q-projl ∘ u
            ≈⟨ ≈.sym (eq-u) ⟩
              p-projl
            ≈⟨ ≈.sym id-r ⟩
              p-projl ∘ id
            ∎
