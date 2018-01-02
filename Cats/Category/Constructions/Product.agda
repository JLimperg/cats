module Cats.Category.Constructions.Product where

open import Data.Bool using (Bool ; true ; false ; not)
open import Level

open import Cats.Category.Base
open import Cats.Functor
open import Cats.Util.Conv
open import Cats.Util.Logic.Constructive

import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Constructions.Terminal as Terminal
import Cats.Category.Constructions.Unique as Unique


module Build {lo la l≈} (Cat : Category lo la l≈) where

  private open module Cat = Category Cat
  open Cat.≈-Reasoning
  open Iso.Build Cat
  open Unique.Build Cat


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

  open BinaryProduct using (projl ; projr ; isBinaryProduct)


  instance
    HasObj-BinaryProduct : ∀ {A B} → HasObj (BinaryProduct A B) lo la l≈
    HasObj-BinaryProduct = record { Cat = Cat ; _ᴼ = BinaryProduct.prod }


  [_]⟨_,_⟩ : ∀ {A B} (A×B : BinaryProduct A B) {Z} → Z ⇒ A → Z ⇒ B → Z ⇒ A×B ᴼ
  [ A×B ]⟨ f , g ⟩ = isBinaryProduct A×B f g ⃗


  ⟨,⟩-projl : ∀ {A B} (A×B : BinaryProduct A B) {Z}
    → {f : Z ⇒ A} {g : Z ⇒ B}
    → projl A×B ∘ [ A×B ]⟨ f , g ⟩ ≈ f
  ⟨,⟩-projl A×B {f = f} {g}
      = ≈.sym (∧-eliml (∃!′.prop (isBinaryProduct A×B f g)))


  ⟨,⟩-projr : ∀ {A B} (A×B : BinaryProduct A B) {Z}
    → {f : Z ⇒ A} {g : Z ⇒ B}
    → projr A×B ∘ [ A×B ]⟨ f , g ⟩ ≈ g
  ⟨,⟩-projr A×B {f = f} {g}
      = ≈.sym (∧-elimr (∃!′.prop (isBinaryProduct A×B f g)))


  ⟨,⟩-resp : ∀ {A B} (A×B : BinaryProduct A B) {Z}
    → {f f′ : Z ⇒ A} {g g′ : Z ⇒ B}
    → f ≈ f′
    → g ≈ g′
    → [ A×B ]⟨ f , g ⟩ ≈ [ A×B ]⟨ f′ , g′ ⟩
  ⟨,⟩-resp A×B {f = f} {g = g} f≈f′ g≈g′
      = ∃!′.unique (isBinaryProduct A×B f g)
        ( ≈.trans f≈f′ (≈.sym (⟨,⟩-projl A×B))
        , ≈.trans g≈g′ (≈.sym (⟨,⟩-projr A×B)))


  ⟨,⟩-∘ : ∀ {A B} (A×B : BinaryProduct A B) {Y Z}
    → {f : Y ⇒ Z} {g : Z ⇒ A} {h : Z ⇒ B}
    → [ A×B ]⟨ g , h ⟩ ∘ f ≈ [ A×B ]⟨ g ∘ f , h ∘ f ⟩
  ⟨,⟩-∘ A×B {f = f} {g} {h} = ≈.sym
      (∃!′.unique
        (isBinaryProduct A×B (g ∘ f) (h ∘ f))
        (≈.sym lem₁ , ≈.sym lem₂))
    where
      lem₁ : projl A×B ∘ [ A×B ]⟨ g , h ⟩ ∘ f ≈ g ∘ f
      lem₁
          = begin
              projl A×B ∘ [ A×B ]⟨ g , h ⟩ ∘ f
            ≈⟨ unassoc ⟩
              (projl A×B ∘ [ A×B ]⟨ g , h ⟩) ∘ f
            ≈⟨ ∘-resp-l (⟨,⟩-projl A×B) ⟩
              g ∘ f
            ∎

      lem₂ : projr A×B ∘ [ A×B ]⟨ g , h ⟩ ∘ f ≈ h ∘ f
      lem₂
          = begin
              projr A×B ∘ [ A×B ]⟨ g , h ⟩ ∘ f
            ≈⟨ unassoc ⟩
              (projr A×B ∘ [ A×B ]⟨ g , h ⟩) ∘ f
            ≈⟨ ∘-resp-l (⟨,⟩-projr A×B) ⟩
              h ∘ f
            ∎


  [_][_]⟨_×_⟩ :
    ∀ {A B} (A×B : BinaryProduct A B)
      {A′ B′} (A′×B′ : BinaryProduct A′ B′)
    → (A ⇒ A′)
    → (B ⇒ B′)
    → A×B ᴼ ⇒ A′×B′ ᴼ
  [ A×B ][ A′×B′ ]⟨ f × g ⟩ = [ A′×B′ ]⟨ f ∘ projl A×B , g ∘ projr A×B ⟩


  ⟨×⟩-resp :
    ∀ {A B} (A×B : BinaryProduct A B)
      {A′ B′} (A′×B′ : BinaryProduct A′ B′)
    → {f f′ : A ⇒ A′}
    → {g g′ : B ⇒ B′}
    → f ≈ f′
    → g ≈ g′
    → [ A×B ][ A′×B′ ]⟨ f × g ⟩ ≈ [ A×B ][ A′×B′ ]⟨ f′ × g′ ⟩
  ⟨×⟩-resp A×B A′×B′ f≈f′ g≈g′ = ⟨,⟩-resp A′×B′ (∘-resp-l f≈f′) (∘-resp-l g≈g′)


  ⟨×⟩-projl :
    ∀ {A B} (A×B : BinaryProduct A B)
      {A′ B′} (A′×B′ : BinaryProduct A′ B′)
    → {f : A ⇒ A′}
    → {g : B ⇒ B′}
    → projl A′×B′ ∘ [ A×B ][ A′×B′ ]⟨ f × g ⟩ ≈ f ∘ projl A×B
  ⟨×⟩-projl A×B A′×B′ = ⟨,⟩-projl A′×B′


  ⟨×⟩-projr :
    ∀ {A B} (A×B : BinaryProduct A B)
      {A′ B′} (A′×B′ : BinaryProduct A′ B′)
    → {f : A ⇒ A′}
    → {g : B ⇒ B′}
    → projr A′×B′ ∘ [ A×B ][ A′×B′ ]⟨ f × g ⟩ ≈ g ∘ projr A×B
  ⟨×⟩-projr A×B A′×B′ = ⟨,⟩-projr A′×B′


  ⟨×⟩-∘ :
    ∀ {A B} (A×B : BinaryProduct A B)
      {A′ B′} (A′×B′ : BinaryProduct A′ B′)
      {A″ B″} (A″×B″ : BinaryProduct A″ B″)
      {f : A′ ⇒ A″}
      {g : B′ ⇒ B″}
      {f′ : A ⇒ A′}
      {g′ : B ⇒ B′}
    → [ A′×B′ ][ A″×B″ ]⟨ f × g ⟩ ∘ [ A×B ][ A′×B′ ]⟨ f′ × g′ ⟩
    ≈ [ A×B ][ A″×B″ ]⟨ f ∘ f′ × g ∘ g′ ⟩
  ⟨×⟩-∘ {A} {B} A×B {A′} {B′} A′×B′ {A″} {B″} A″×B″ {f} {g} {f′} {g′}
      = begin
          [ A″×B″ ]⟨ f ∘ projl A′×B′ , g ∘ projr A′×B′ ⟩ ∘
          [ A′×B′ ]⟨ f′ ∘ projl A×B  , g′ ∘ projr A×B  ⟩
        ≈⟨ ⟨,⟩-∘ A″×B″ ⟩
          [ A″×B″ ]⟨
            (f ∘ projl A′×B′) ∘ [ A′×B′ ]⟨ f′ ∘ projl A×B , g′ ∘ projr A×B ⟩
          , (g ∘ projr A′×B′) ∘ [ A′×B′ ]⟨ f′ ∘ projl A×B , g′ ∘ projr A×B ⟩
          ⟩
        ≈⟨ ⟨,⟩-resp A″×B″ assoc assoc ⟩
          [ A″×B″ ]⟨
            f ∘ (projl A′×B′ ∘ [ A′×B′ ]⟨ f′ ∘ projl A×B , g′ ∘ projr A×B ⟩)
          , g ∘ (projr A′×B′ ∘ [ A′×B′ ]⟨ f′ ∘ projl A×B , g′ ∘ projr A×B ⟩)
          ⟩
        ≈⟨ ⟨,⟩-resp A″×B″ (∘-resp-r (⟨,⟩-projl A′×B′)) (∘-resp-r (⟨,⟩-projr A′×B′)) ⟩
          [ A″×B″ ]⟨
            f ∘ (f′ ∘ projl A×B)
          , g ∘ (g′ ∘ projr A×B)
          ⟩
        ≈⟨ ⟨,⟩-resp A″×B″ unassoc unassoc ⟩
          [ A″×B″ ]⟨
              (f ∘ f′) ∘ projl A×B
            , (g ∘ g′) ∘ projr A×B
          ⟩
        ∎


  -- TODO Generalise _-×-_ and ⟨_,_⟩ to non-binary products. This should make
  -- the duplication in the associated lemmas go away.


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
            ≈⟨ ≈.sym assoc ⟩
              (proj i ∘ v) ∘ u
            ≈⟨ ∘-resp-l (≈.sym (v-eq _)) ⟩
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
            ≈⟨ unassoc ⟩
              (proj i ∘ v) ∘ u
            ≈⟨ ∘-resp-l (≈.sym (v-eq _)) ⟩
              (f₂ ∘ proj′ (perm i)) ∘ u
            ≈⟨ assoc ⟩
              f₂ ∘ proj′ (perm i) ∘ u
            ≈⟨ ∘-resp-r (≈.sym (u-eq _)) ⟩
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
            ≈⟨ unassoc ⟩
              (proj′ i ∘ u) ∘ v
            ≈⟨ ∘-resp-l (≈.sym (u-eq _)) ⟩
              (f₁ ∘ proj (perm i)) ∘ v
            ≈⟨ assoc ⟩
              f₁ ∘ proj (perm i) ∘ v
            ≈⟨ ∘-resp-r (≈.sym (v-eq _)) ⟩
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
          (λ { {true} → id ; {false} → id })
          (λ { {true} → id ; {false} → id })
          (λ { {true} → ≈.trans id-l id-l ; {false} → ≈.trans id-l id-l })
          (λ { {true} → ≈.trans id-l id-l ; {false} → ≈.trans id-l id-l })


record HasBinaryProducts {lo la l≈} (C : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈)
  where
  private open module Bld = Build C using (BinaryProduct)
  open Category C

  infixr 2 _×_ _×′_ ⟨_×_⟩ ⟨_,_⟩

  field
    _×′_ : ∀ A B → BinaryProduct A B


  _×_ : Obj → Obj → Obj
  A × B = BinaryProduct.prod (A ×′ B)


  projl : ∀ {A B} → A × B ⇒ A
  projl {A} {B} = BinaryProduct.projl (A ×′ B)


  projr : ∀ {A B} → A × B ⇒ B
  projr {A} {B} = BinaryProduct.projr (A ×′ B)


  ⟨_,_⟩ : ∀ {A B Z} → Z ⇒ A → Z ⇒ B → Z ⇒ A × B
  ⟨_,_⟩ {A} {B} = Bld.[ A ×′ B ]⟨_,_⟩


  ⟨_×_⟩ : ∀ {A B A′ B′} → A ⇒ A′ → B ⇒ B′ → A × B ⇒ A′ × B′
  ⟨_×_⟩ {A} {B} {A′} {B′} = Bld.[ A ×′ B ][ A′ ×′ B′ ]⟨_×_⟩


  ⟨,⟩-resp : ∀ {A B Z} {f f′ : Z ⇒ A} {g g′ : Z ⇒ B}
    → f ≈ f′
    → g ≈ g′
    → ⟨ f , g ⟩ ≈ ⟨ f′ , g′ ⟩
  ⟨,⟩-resp {A} {B} = Bld.⟨,⟩-resp (A ×′ B)


  ⟨,⟩-projl : ∀ {A B Z} {f : Z ⇒ A} {g : Z ⇒ B} → projl ∘ ⟨ f , g ⟩ ≈ f
  ⟨,⟩-projl {A} {B} = Bld.⟨,⟩-projl (A ×′ B)


  ⟨,⟩-projr : ∀ {A B Z} {f : Z ⇒ A} {g : Z ⇒ B} → projr ∘ ⟨ f , g ⟩ ≈ g
  ⟨,⟩-projr {A} {B} = Bld.⟨,⟩-projr (A ×′ B)


  ⟨,⟩-∘ : ∀ {A B Y Z} {f : Y ⇒ Z} {g : Z ⇒ A} {h : Z ⇒ B}
    → ⟨ g , h ⟩ ∘ f ≈ ⟨ g ∘ f , h ∘ f ⟩
  ⟨,⟩-∘ {A} {B} = Bld.⟨,⟩-∘ (A ×′ B)


  ⟨×⟩-resp : ∀ {A A′ B B′} {f f′ : A ⇒ A′} {g g′ : B ⇒ B′}
    → f ≈ f′
    → g ≈ g′
    → ⟨ f × g ⟩ ≈ ⟨ f′ × g′ ⟩
  ⟨×⟩-resp {A} {A′} {B} {B′} = Bld.⟨×⟩-resp (A ×′ B) (A′ ×′ B′)


  ⟨×⟩-projl : ∀ {A A′ B B′} {f : A ⇒ A′} {g : B ⇒ B′}
    → projl ∘ ⟨ f × g ⟩ ≈ f ∘ projl
  ⟨×⟩-projl {A} {A′} {B} {B′} = Bld.⟨×⟩-projl (A ×′ B) (A′ ×′ B′)


  ⟨×⟩-projr : ∀ {A A′ B B′} {f : A ⇒ A′} {g : B ⇒ B′}
    → projr ∘ ⟨ f × g ⟩ ≈ g ∘ projr
  ⟨×⟩-projr {A} {A′} {B} {B′} = Bld.⟨×⟩-projr (A ×′ B) (A′ ×′ B′)


  ⟨×⟩-∘ : ∀ {A A′ A″ B B′ B″}
    → {f : A′ ⇒ A″} {f′ : A ⇒ A′} {g : B′ ⇒ B″} {g′ : B ⇒ B′}
    → ⟨ f × g ⟩ ∘ ⟨ f′ × g′ ⟩ ≈ ⟨ f ∘ f′ × g ∘ g′ ⟩
  ⟨×⟩-∘ {A} {A′} {A″} {B} {B′} {B″} = Bld.⟨×⟩-∘ (A ×′ B) (A′ ×′ B′) (A″ ×′ B″)


record HasFiniteProducts {lo la l≈} (Cat : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈)
  where
  open Terminal using (HasTerminal)

  field
    {{hasTerminal}} : HasTerminal Cat
    {{hasBinaryProducts}} : HasBinaryProducts Cat

  open HasTerminal hasTerminal public
  open HasBinaryProducts hasBinaryProducts public


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈}
  {D : Category lo′ la′ l≈′}
  where

  open Category C
  open Build using (IsBinaryProduct ; IsProduct)
  open Functor


  PreservesBinaryProducts : (F : Functor C D) → Set _
  PreservesBinaryProducts F
    = ∀ {A B A×B} {projl : A×B ⇒ A} {projr : A×B ⇒ B}
    → IsBinaryProduct C A×B projl projr
    → IsBinaryProduct D (fobj F A×B) (fmap F projl) (fmap F projr)


  PreservesProducts : ∀ {i} (I : Set i) (F : Functor C D) → Set _
  PreservesProducts I F
    = ∀ {O : I → Obj} {P} {proj : ∀ i → P ⇒ O i}
    → IsProduct C O P proj
    → IsProduct D (λ i → fobj F (O i)) (fobj F P) (λ i → fmap F (proj i))
