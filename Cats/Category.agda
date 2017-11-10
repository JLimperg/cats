module Cats.Category where

open import Data.Bool using (Bool ; true ; false ; not)
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


  ∃!→unique : ∀ {lp} {A B} {P : A ⇒ B → Set lp}
    → ∃! P
    → {f g : A ⇒ B}
    → P f
    → P g
    → f ≈ g
  ∃!→unique (u , pu , u-unique) pf pg
      = ≈.trans (≈.sym (u-unique pf)) (u-unique pg)


  IsMono : ∀ {A B} → A ⇒ B → Set (lo ⊔ la ⊔ l≈)
  IsMono {A} f = ∀ {C} {g h : C ⇒ A} → f ∘ g ≈ f ∘ h → g ≈ h


  IsEpi : ∀ {A B} → A ⇒ B → Set (lo ⊔ la ⊔ l≈)
  IsEpi {A} {B} f = ∀ {C} {g h : B ⇒ C} → g ∘ f ≈ h ∘ f → g ≈ h


  iso-mono : ∀ {A B} (iso : A ≅ B) → IsMono (forth iso)
  iso-mono iso {g = g} {h} iso∘g≈iso∘h
      = begin
          g
        ≈⟨ ≈.sym id-l ⟩
          id ∘ g
        ≈⟨ ∘-resp (≈.sym (back-forth iso)) ≈.refl ⟩
          (back iso ∘ forth iso) ∘ g
        ≈⟨ assoc _ _ _ ⟩
          back iso ∘ forth iso ∘ g
        ≈⟨ ∘-resp ≈.refl iso∘g≈iso∘h ⟩
          back iso ∘ forth iso ∘ h
        ≈⟨ ≈.sym (assoc _ _ _) ⟩
          (back iso ∘ forth iso) ∘ h
        ≈⟨ ∘-resp (back-forth iso) ≈.refl ⟩
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
        ≈⟨ ∘-resp ≈.refl (≈.sym (forth-back iso)) ⟩
          g ∘ forth iso ∘ back iso
        ≈⟨ ≈.sym (assoc _ _ _) ⟩
          (g ∘ forth iso) ∘ back iso
        ≈⟨ ∘-resp g∘iso≈h∘iso ≈.refl ⟩
          (h ∘ forth iso) ∘ back iso
        ≈⟨ assoc _ _ _ ⟩
          h ∘ forth iso ∘ back iso
        ≈⟨ ∘-resp ≈.refl (forth-back iso) ⟩
          h ∘ id
        ≈⟨ id-r ⟩
          h
        ∎


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


  -- TODO reformulate initiality and terminality in terms of ∃!
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


  Initial⇒X-unique : ∀ {Zero} → IsInitial Zero → ∀ {X} {f g : Zero ⇒ X} → f ≈ g
  Initial⇒X-unique init {X} {f} {g} with init X
  ... | x , x-uniq = ≈.trans (≈.sym (x-uniq _)) (x-uniq _)


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


  X⇒Terminal-unique : ∀ {One} → IsTerminal One → ∀ {X} {f g : X ⇒ One} → f ≈ g
  X⇒Terminal-unique term {X} {f} {g} with term X
  ... | x , x-uniq = ≈.trans (≈.sym (x-uniq _)) (x-uniq _)


  IsProduct : ∀ {li} {I : Set li} (O : I → Obj) P → (∀ i → P ⇒ O i)
    → Set (lo ⊔ la ⊔ l≈ ⊔ li)
  IsProduct O P proj
      = ∀ {X} (x : ∀ i → X ⇒ O i) → ∃![ u ] (∀ i → x i ≈ proj i ∘ u)


  record Product {li} {I : Set li} (O : I → Obj) : Set (lo ⊔ la ⊔ l≈ ⊔ li) where
    field
      prod : Obj
      proj : ∀ i → prod ⇒ O i
      isProduct : IsProduct O prod proj


  IsBinaryProduct : ∀ {A B} P → (P ⇒ A) → (P ⇒ B) → Set (lo ⊔ la ⊔ l≈)
  IsBinaryProduct {A} {B} P projl projr
      = ∀ {X} (xl : X ⇒ A) (xr : X ⇒ B) → ∃![ u ] (xl ≈ projl ∘ u ∧ xr ≈ projr ∘ u)


  record BinaryProduct (A B : Obj) : Set (lo ⊔ la ⊔ l≈) where
    field
      prod : Obj
      projl : prod ⇒ A
      projr : prod ⇒ B
      isBinaryProduct : IsBinaryProduct prod projl projr


  Bool-elim : ∀ {a} {A : Bool → Set a} → A true → A false → (b : Bool) → A b
  Bool-elim x y true  = x
  Bool-elim x y false = y


  IsProduct→IsBinaryProduct : ∀ {A B P proj}
    → IsProduct (Bool-elim A B) P proj
    → IsBinaryProduct P (proj true) (proj false)
  IsProduct→IsBinaryProduct prod xl xr with prod (Bool-elim xl xr)
  ... | u , u-eq , u-uniq
      = u
      , (u-eq true , u-eq false)
      , λ { (h₁ , h₂) → u-uniq (Bool-elim h₁ h₂) }


  IsBinaryProduct→IsProduct : ∀ {A B P projl projr}
    → IsBinaryProduct P projl projr
    → IsProduct (Bool-elim A B) P (Bool-elim projl projr)
  IsBinaryProduct→IsProduct prod proj with prod (proj true) (proj false)
  ... | u , (u-eq₁ , u-eq₂) , u-uniq
      = u , Bool-elim u-eq₁ u-eq₂ , λ eq → u-uniq (eq true , eq false)


  proj-cancel : ∀ {li} {I : Set li} {O : I → Obj} {P proj}
    → IsProduct O P proj
    → ∀ {X} {f g : X ⇒ P}
    → (∀ i → proj i ∘ f ≈ proj i ∘ g)
    → f ≈ g
  proj-cancel {proj = proj} prod {f = f} {g} eq with prod (λ i → proj i ∘ g)
  ... | u , _ , u-uniq
      = begin
          f
        ≈⟨ ≈.sym (u-uniq (λ i → ≈.sym (eq i))) ⟩
          u
        ≈⟨ u-uniq (λ i → ≈.refl) ⟩
          g
        ∎


  Product-unique : ∀ {li} {I : Set li} {O : I → Obj} {P proj}
    → IsProduct O P proj
    → ∀  {P′ proj′}
    → IsProduct O P′ proj′
    → P ≅ P′
  Product-unique {P = P} {proj} prod {P′} {proj′} prod′
    with prod′ proj | prod proj′
  ... | u , u-eq , _ | v , v-eq , _ = record
      { forth = u
      ; back = v
      ; back-forth = proj-cancel prod (lemma u-eq v-eq)
      ; forth-back = proj-cancel prod′ (lemma v-eq u-eq)
      }
    where
      lemma : ∀ {li} {I : Set li} {O : I → Obj} {P P′ : Obj}
        → {proj : ∀ i → P ⇒ O i} {proj′ : ∀ i → P′ ⇒ O i}
        → ∀ {u v}
        → (∀ i → proj i ≈ proj′ i ∘ u)
        → (∀ i → proj′ i ≈ proj i ∘ v)
        → ∀ i → proj i ∘ v ∘ u ≈ proj i ∘ id
      lemma {P = P} {P′} {proj} {proj′} {u} {v} u-eq v-eq i
          = begin
              proj i ∘ v ∘ u
            ≈⟨ ≈.sym (assoc _ _ _)  ⟩
              (proj i ∘ v) ∘ u
            ≈⟨ ∘-resp (≈.sym (v-eq _)) ≈.refl ⟩
              proj′ i ∘ u
            ≈⟨ ≈.sym (u-eq _) ⟩
              proj i
            ≈⟨ ≈.sym id-r ⟩
              proj i ∘ id
            ∎


  -- TODO eliminate duplication in lemmas
  Product-permute : ∀ {li} {I : Set li}
    → (perm : I → I)
    → ∀ {O : I → Obj} {P proj}
    → IsProduct O P proj
    → ∀ {O′ : I → Obj} {P′ proj′}
    → IsProduct O′ P′ proj′
    → (f₁ : ∀ {i} → O (perm i) ⇒ O′ i)
    → (f₂ : ∀ {i} → O′ (perm i) ⇒ O i)
    → (∀ {i} → f₂ ∘ f₁ ∘ proj (perm (perm i)) ≈ proj i)
    → (∀ {i} → f₁ ∘ f₂ ∘ proj′ (perm (perm i)) ≈ proj′ i)
    → P ≅ P′
  Product-permute perm {O} {P} {proj} prod {O′} {P′} {proj′} prod′ f₁ f₂ eq₁ eq₂
    with prod′ {P} (λ i → f₁ ∘ proj (perm i))
       | prod {P′} (λ i → f₂ ∘ proj′ (perm i))
  ... | u , u-eq , _ | v , v-eq , _
      = record
      { forth = u
      ; back = v
      ; back-forth = proj-cancel prod lem₁
      ; forth-back = proj-cancel prod′ lem₂
      }
    where
      lem₁ : ∀ i → proj i ∘ v ∘ u ≈ proj i ∘ id
      lem₁ i
          = begin
              proj i ∘ v ∘ u
            ≈⟨ ≈.sym (assoc _ _ _) ⟩
              (proj i ∘ v) ∘ u
            ≈⟨ ∘-resp (≈.sym (v-eq _)) ≈.refl ⟩
              (f₂ ∘ proj′ (perm i)) ∘ u
            ≈⟨ assoc _ _ _ ⟩
              f₂ ∘ proj′ (perm i) ∘ u
            ≈⟨ ∘-resp ≈.refl (≈.sym (u-eq _)) ⟩
              f₂ ∘ f₁ ∘ proj (perm (perm i))
            ≈⟨ eq₁ ⟩
              proj i
            ≈⟨ ≈.sym id-r ⟩
              proj i ∘ id
            ∎

      lem₂ : ∀ i → proj′ i ∘ u ∘ v ≈ proj′ i ∘ id
      lem₂ i
          = begin
              proj′ i ∘ u ∘ v
            ≈⟨ ≈.sym (assoc _ _ _) ⟩
              (proj′ i ∘ u) ∘ v
            ≈⟨ ∘-resp (≈.sym (u-eq _)) ≈.refl ⟩
              (f₁ ∘ proj (perm i)) ∘ v
            ≈⟨ assoc _ _ _ ⟩
              f₁ ∘ proj (perm i) ∘ v
            ≈⟨ ∘-resp ≈.refl (≈.sym (v-eq _)) ⟩
              f₁ ∘ f₂ ∘ proj′ (perm (perm i))
            ≈⟨ eq₂ ⟩
              proj′ i
            ≈⟨ ≈.sym id-r ⟩
              proj′ i ∘ id
            ∎


  BinaryProduct-commute : ∀ {A B P pl pr Q ql qr}
    → IsBinaryProduct {A} {B} P pl pr
    → IsBinaryProduct {B} {A} Q ql qr
    → P ≅ Q
  BinaryProduct-commute prod prod′
      = Product-permute
          not
          (IsBinaryProduct→IsProduct prod)
          (IsBinaryProduct→IsProduct prod′)
          (λ { {true} → id ; {false} → id})
          (λ { {true} → id ; {false} → id})
          (λ { {true} → ≈.trans id-l id-l ; {false} → ≈.trans id-l id-l })
          (λ { {true} → ≈.trans id-l id-l ; {false} → ≈.trans id-l id-l })


  record IsEqualizer {A B} (f g : A ⇒ B) {E} (e : E ⇒ A)
    : Set (lo ⊔ la ⊔ l≈) where
    field
      equalizes : f ∘ e ≈ g ∘ e
      universal : ∀ {Z} (z : Z ⇒ A)
        → f ∘ z ≈ g ∘ z
        → ∃![ u ] (e ∘ u ≈ z)


  record Equalizer {A B} (f g : A ⇒ B) : Set (lo ⊔ la ⊔ l≈) where
    field
      {E} : Obj
      e : E ⇒ A
      isEqualizer : IsEqualizer f g e

    open IsEqualizer isEqualizer public


  equalizer→mono : ∀ {A B} {f g : A ⇒ B} {E} {e : E ⇒ A}
    → IsEqualizer f g e
    → IsMono e
  equalizer→mono {f = f} {g} {E} {e} eql {Z} {i} {j} e∘i≈e∘j
      = ∃!→unique (universal (e ∘ j) lemma) e∘i≈e∘j ≈.refl
    where
      open module E = IsEqualizer eql

      lemma : f ∘ e ∘ j ≈ g ∘ e ∘ j
      lemma
          = begin
            f ∘ e ∘ j
          ≈⟨ ≈.sym (assoc _ _ _) ⟩
            (f ∘ e) ∘ j
          ≈⟨ ∘-resp equalizes ≈.refl ⟩
            (g ∘ e) ∘ j
          ≈⟨ assoc _ _ _ ⟩
            g ∘ e ∘ j
          ∎
