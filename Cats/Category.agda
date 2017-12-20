module Cats.Category where

open import Data.Bool using (Bool ; true ; false ; not)
open import Level
open import Relation.Binary using
  (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_ ; Setoid)

open import Cats.Util.Logic.Constructive

import Relation.Binary.EqReasoning as EqReasoning

import Cats.Category.Base as Base
import Cats.Category.Constructions.Epi as Epi
import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Constructions.Initial as Initial
import Cats.Category.Constructions.Mono as Mono
import Cats.Category.Constructions.Terminal as Terminal
import Cats.Category.Constructions.Unique as Unique


Category : ∀ lo la l≈ → Set (suc (lo ⊔ la ⊔ l≈))
Category = Base.Category


module Category {lo la l≈} (Cat : Base.Category lo la l≈) where

  private open module Cat = Base.Category Cat public
  open Cat.≈-Reasoning
  open Epi.Build Cat public
  open Initial.Build Cat public
  open Iso.Build Cat public
  open Mono.Build Cat public
  open Terminal.Build Cat public
  open Unique.Build Cat public
  open _≅_


  _∘ʳ_ : ∀ {A B C} → A ⇒ B → B ⇒ C → A ⇒ C
  f ∘ʳ g = g ∘ f


  -- Note: f unique and g unique does not, in general, imply g ∘ f unique. There
  -- can be an h : A ⇒ C which is different from g′ ∘ f′ for any f′, g′.
  ∘-unique : ∀ {A B C} {g : B ⇒ C} {f : A ⇒ B}
    → IsUnique g
    → IsUnique f
    → ∀ {g′ : B ⇒ C} {f′ : A ⇒ B}
    → g ∘ f ≈ g′ ∘ f′
  ∘-unique uniq-g uniq-f = ∘-resp (uniq-g _) (uniq-f _)


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
  ... | ∃!-intro u u-eq u-uniq
      = ∃!-intro
          u
          (u-eq true , u-eq false)
          (λ { (h₁ , h₂) → u-uniq (Bool-elim h₁ h₂) })


  IsBinaryProduct→IsProduct : ∀ {A B P projl projr}
    → IsBinaryProduct P projl projr
    → IsProduct (Bool-elim A B) P (Bool-elim projl projr)
  IsBinaryProduct→IsProduct prod proj with prod (proj true) (proj false)
  ... | ∃!-intro u (u-eq₁ , u-eq₂) u-uniq
      = ∃!-intro
          u
          (Bool-elim u-eq₁ u-eq₂)
          (λ eq → u-uniq (eq true , eq false))


  proj-cancel : ∀ {li} {I : Set li} {O : I → Obj} {P proj}
    → IsProduct O P proj
    → ∀ {X} {f g : X ⇒ P}
    → (∀ i → proj i ∘ f ≈ proj i ∘ g)
    → f ≈ g
  proj-cancel {proj = proj} prod {f = f} {g} eq with prod (λ i → proj i ∘ g)
  ... | ∃!-intro u _ u-uniq
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
  ... | ∃!-intro u u-eq _ | ∃!-intro v v-eq _ = record
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
  ... | ∃!-intro u u-eq _ | ∃!-intro v v-eq _
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
      = ∃!→≈ (universal (e ∘ j) lemma) e∘i≈e∘j ≈.refl
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
