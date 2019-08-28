{-# OPTIONS --without-K --safe #-}
module Cats.Category.Constructions.Product where

open import Data.Bool using (Bool ; true ; false ; not)
open import Level

open import Cats.Category.Base
open import Cats.Category.Constructions.Terminal as Terminal using (HasTerminal)
open import Cats.Functor using (Functor)
open import Cats.Util.Conv
open import Cats.Util.Logic.Constructive

import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Constructions.Unique as Unique


Bool-elim : ∀ {a} {A : Bool → Set a} → A true → A false → (i : Bool) → A i
Bool-elim x y true = x
Bool-elim x y false = y


module Build {lo la l≈} (Cat : Category lo la l≈) where

  private open module Cat = Category Cat
  open Cat.≈-Reasoning
  open Iso.Build Cat
  open Unique.Build Cat
  open Terminal.Build Cat


  IsProduct : ∀ {li} {I : Set li} (O : I → Obj) P → (∀ i → P ⇒ O i)
    → Set (lo ⊔ la ⊔ l≈ ⊔ li)
  IsProduct O P proj
      = ∀ {X} (x : ∀ i → X ⇒ O i) → ∃![ u ] (∀ i → x i ≈ proj i ∘ u)


  -- TODO The types of the equalities in IsBinaryProducts are backwards, since
  -- we want the RHS to be simpler than the LHS. So, projl ∘ u ≈ xl instead
  -- of xl ≈ projl ∘ u.
  IsBinaryProduct : ∀ {A B} P → (P ⇒ A) → (P ⇒ B) → Set (lo ⊔ la ⊔ l≈)
  IsBinaryProduct {A} {B} P projl projr
      = ∀ {X} (xl : X ⇒ A) (xr : X ⇒ B)
        → ∃![ u ] (xl ≈ projl ∘ u ∧ xr ≈ projr ∘ u)


  IsBinaryProduct→IsProduct : ∀ {A B P} {pl : P ⇒ A} {pr : P ⇒ B}
    → IsBinaryProduct P pl pr
    → IsProduct (Bool-elim A B) P (Bool-elim pl pr)
  IsBinaryProduct→IsProduct isBinProd x = record
      { arr = f ⃗
      ; prop = Bool-elim (∧-eliml (∃!′.prop f)) (∧-elimr (∃!′.prop f))
      ; unique = λ eq → ∃!′.unique f (eq true , eq false)
      }
    where
      f = isBinProd (x true) (x false)


  record Product {li} {I : Set li} (O : I → Obj) : Set (lo ⊔ la ⊔ l≈ ⊔ li) where
    field
      prod : Obj
      proj : ∀ i → prod ⇒ O i
      isProduct : IsProduct O prod proj


  open Product using (proj ; isProduct)


  instance
    HasObj-Product : ∀ {li} {I : Set li} {O : I → Obj}
      → HasObj (Product O) lo la l≈
    HasObj-Product = record { Cat = Cat ; _ᴼ = Product.prod }


  BinaryProduct : Obj → Obj → Set (lo ⊔ la ⊔ l≈)
  BinaryProduct A B = Product (Bool-elim A B)


  mkBinaryProduct : ∀ {A B P} (pl : P ⇒ A) (pr : P ⇒ B)
    → IsBinaryProduct P pl pr
    → BinaryProduct A B
  mkBinaryProduct {P = P} pl pr isBinProd = record
      { isProduct = IsBinaryProduct→IsProduct isBinProd }


  nullaryProduct-Terminal : (P : Product {I = ⊥} (λ())) → IsTerminal (P ᴼ)
  nullaryProduct-Terminal P X with isProduct P {X = X} λ()
  ... | ∃!-intro arr _ unique = ∃!-intro arr _ (λ _ → unique λ())


  module _ {li} {I : Set li} {O : I → Obj} (P : Product O) where

    factorizer : ∀ {X} → (∀ i → X ⇒ O i) → X ⇒ P ᴼ
    factorizer proj = isProduct P proj ⃗


    factorizer-unique : ∀ {X} (fact : X ⇒ P ᴼ)
      → {x : ∀ i → X ⇒ O i}
      → (∀ i → x i ≈ proj P i ∘ fact)
      → factorizer x ≈ fact
    factorizer-unique fact {x} eq = ∃!′.unique (isProduct P x) eq


    factorizer-proj : ∀ {X} {x : ∀ i → X ⇒ O i} {i}
      → proj P i ∘ factorizer x ≈ x i
    factorizer-proj {x = x} {i} = ≈.sym (∃!′.prop (isProduct P x) i)


    factorizer-resp : ∀ {X} {x y : ∀ i → X ⇒ O i}
      → (∀ i → x i ≈ y i)
      → factorizer x ≈ factorizer y
    factorizer-resp {x = x} {y} eq = factorizer-unique (factorizer y)
      λ i → ≈.trans (eq _) (≈.sym factorizer-proj)


    factorizer-∘ : ∀ {X} {x : ∀ i → X ⇒ O i} {Z} {f : Z ⇒ X}
      → factorizer x ∘ f ≈ factorizer (λ i → x i ∘ f)
    factorizer-∘ {x = x} {f = f} = ≈.sym
      (factorizer-unique (factorizer x ∘ f)
        λ _ → ≈.sym (≈.trans unassoc (∘-resp-l factorizer-proj)))


    factorizer-id : factorizer (proj P) ≈ id
    factorizer-id = factorizer-unique id λ i → ≈.sym id-r


  module _ {li} {I : Set li}
    {O : I → Obj}  (P : Product O)
    {O′ : I → Obj} (P′ : Product O′)
    where

    times : (∀ i → O i ⇒ O′ i) → P ᴼ ⇒ P′ ᴼ
    times x = factorizer P′ (λ i → x i ∘ proj P i)


    times-proj : ∀ {x : ∀ i → O i ⇒ O′ i} {i}
      → proj P′ i ∘ times x ≈ x i ∘ proj P i
    times-proj = factorizer-proj P′


    times-resp : {x y : ∀ i → O i ⇒ O′ i}
      → (∀ i → x i ≈ y i)
      → times x ≈ times y
    times-resp {x} {y} eq = factorizer-resp P′ (λ i → ∘-resp-l (eq i))


  times-id : ∀ {li} {I : Set li} {O : I → Obj} (P : Product O)
    → times P P (λ _ → id) ≈ id
  times-id P = factorizer-unique P id λ _ → ≈.trans id-l (≈.sym id-r)


  times-∘ : ∀ {li} {I : Set li}
    → {O O′ O″ : I → Obj}
    → (P : Product O) (P′ : Product O′) (P″ : Product O″)
    → {x : ∀ i → O i ⇒ O′ i} {y : ∀ i → O′ i ⇒ O″ i}
    → times P′ P″ y ∘ times P P′ x ≈ times P P″ (λ i → y i ∘ x i)
  times-∘ P P′ P″ {x} {y} =
    begin
      times P′ P″ y ∘ times P P′ x
    ≈⟨ factorizer-∘ P″ ⟩
      factorizer P″ (λ i → (y i ∘ proj P′ i) ∘ times P P′ x)
    ≈⟨ factorizer-resp P″ (λ i → assoc) ⟩
      factorizer P″ (λ i → y i ∘ proj P′ i ∘ times P P′ x)
    ≈⟨ factorizer-resp P″ (λ i → ∘-resp-r (times-proj P P′)) ⟩
      factorizer P″ (λ i → y i ∘ x i ∘ proj P i)
    ≈⟨ factorizer-resp P″ (λ i → unassoc) ⟩
      times P P″ (λ i → y i ∘ x i)
    ∎


  times-factorizer : ∀ {li} {I : Set li}
    → {O O′ : I → Obj}
    → (P : Product O) (P′ : Product O′)
    → ∀ {X} {x : ∀ i → X ⇒ O i} {y : ∀ i → O i ⇒ O′ i}
    → times P P′ y ∘ factorizer P x ≈ factorizer P′ (λ i → y i ∘ x i)
  times-factorizer P P′
    = ≈.trans (factorizer-∘ P′)
        (factorizer-resp P′ λ i → ≈.trans assoc (∘-resp-r (factorizer-proj P)))


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


open Build public using
  (IsProduct ; IsBinaryProduct ; Product ; BinaryProduct ; HasObj-Product)


record HasProducts {lo la l≈} li (C : Category lo la l≈)
  : Set (suc li ⊔ lo ⊔ la ⊔ l≈ )
  where
  private module Bld = Build C
  open Category C

  field
    Π′ : {I : Set li} (O : I → Obj) → Product C O


  module _ {I : Set li} where

    Π : ∀ (O : I → Obj) → Obj
    Π O = Product.prod (Π′ O)


    syntax Π (λ i → O) = Π[ i ] O


    proj : ∀ {O : I → Obj} i → Π O ⇒ O i
    proj {O} = Bld.Product.proj (Π′ O)


    factorizer : ∀ {O : I → Obj} {X} → (∀ i → X ⇒ O i) → X ⇒ Π O
    factorizer {O} = Bld.factorizer (Π′ O)


    times : ∀ {O O′ : I → Obj} → (∀ i → O i ⇒ O′ i) → Π O ⇒ Π O′
    times {O} {O′} = Bld.times (Π′ O) (Π′ O′)


    factorizer-proj : ∀ {O : I → Obj} {X} {x : ∀ i → X ⇒ O i} {i}
      → proj i ∘ factorizer x ≈ x i
    factorizer-proj {O} = Bld.factorizer-proj (Π′ O)


    factorizer-resp : ∀ {O : I → Obj} {X} {x y : ∀ i → X ⇒ O i}
      → (∀ i → x i ≈ y i)
      → factorizer x ≈ factorizer y
    factorizer-resp {O} = Bld.factorizer-resp (Π′ O)


    factorizer-unique : ∀ {O : I → Obj} {X} {x : ∀ i → X ⇒ O i} {u}
      → (∀ i → x i ≈ proj i ∘ u)
      → factorizer x ≈ u
    factorizer-unique {O} eq = Bld.factorizer-unique (Π′ O) _ eq


    factorizer-∘ : ∀ {O : I → Obj} {X} {x : ∀ i → X ⇒ O i} {Z} {f : Z ⇒ X}
      → factorizer x ∘ f ≈ factorizer (λ i → x i ∘ f)
    factorizer-∘ {O} = Bld.factorizer-∘ (Π′ O)


    factorizer-id : ∀ {O} → factorizer {O} proj ≈ id
    factorizer-id {O} = Bld.factorizer-id (Π′ O)


    times-proj : ∀ {O O′ : I → Obj} {x : ∀ i → O i ⇒ O′ i} {i}
      → proj i ∘ times x ≈ x i ∘ proj i
    times-proj {O} {O′} = Bld.times-proj (Π′ O) (Π′ O′)


    times-resp : ∀ {O O′ : I → Obj} {x y : ∀ i → O i ⇒ O′ i}
      → (∀ i → x i ≈ y i)
      → times x ≈ times y
    times-resp {O} {O′} = Bld.times-resp (Π′ O) (Π′ O′)


    times-id : ∀ {O : I → Obj} → times {O} (λ _ → id) ≈ id
    times-id {O} = Bld.times-id (Π′ O)


    times-∘ : ∀ {O O′ O″ : I → Obj} {x : ∀ i → O i ⇒ O′ i} {y : ∀ i → O′ i ⇒ O″ i}
      → times y ∘ times x ≈ times (λ i → y i ∘ x i)
    times-∘ {O} {O′} {O″} = Bld.times-∘ (Π′ O) (Π′ O′) (Π′ O″)


    times-factorizer : ∀ {O O′ : I → Obj} {X}
      → {x : ∀ i → X ⇒ O i} {y : ∀ i → O i ⇒ O′ i}
      → times y ∘ factorizer x ≈ factorizer (λ i → y i ∘ x i)
    times-factorizer {O} {O′} = Bld.times-factorizer (Π′ O) (Π′ O′)


HasProducts→HasTerminal : ∀ {lo la l≈} {C : Category lo la l≈}
  → HasProducts zero C
  → HasTerminal C
HasProducts→HasTerminal {C = C} record { Π′ = Π }
    = let P = Π {I = ⊥} λ() in
      record
        { ⊤ = Product.prod P
        ; isTerminal = Build.nullaryProduct-Terminal C P
        }


record HasBinaryProducts {lo la l≈} (C : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈)
  where
  private module Bld = Build C
  open Category C
  open ≈-Reasoning

  infixr 2 _×_ _×′_ ⟨_×_⟩ ⟨_,_⟩

  field
    _×′_ : ∀ A B → BinaryProduct C A B


  _×_ : Obj → Obj → Obj
  A × B = (A ×′ B) ᴼ


  projl : ∀ {A B} → A × B ⇒ A
  projl {A} {B} = Product.proj (A ×′ B) true


  projr : ∀ {A B} → A × B ⇒ B
  projr {A} {B} = Product.proj (A ×′ B) false


  ⟨_,_⟩ : ∀ {A B Z} → Z ⇒ A → Z ⇒ B → Z ⇒ A × B
  ⟨_,_⟩ {A} {B} f g
      = Bld.factorizer (A ×′ B) (Bool-elim f g)


  ⟨_×_⟩ : ∀ {A B A′ B′} → A ⇒ A′ → B ⇒ B′ → A × B ⇒ A′ × B′
  ⟨_×_⟩ {A} {B} {A′} {B′} f g
      = Bld.times (A ×′ B) (A′ ×′ B′) (Bool-elim f g)


  first : ∀ {A A′ B} → A ⇒ A′ → A × B ⇒ A′ × B
  first f = ⟨ f × id ⟩


  second : ∀ {A B B′} → B ⇒ B′ → A × B ⇒ A × B′
  second f = ⟨ id × f ⟩


  swap : ∀ {A B} → A × B ⇒ B × A
  swap = ⟨ projr , projl ⟩


  ⟨,⟩-resp : ∀ {A B Z} {f f′ : Z ⇒ A} {g g′ : Z ⇒ B}
    → f ≈ f′
    → g ≈ g′
    → ⟨ f , g ⟩ ≈ ⟨ f′ , g′ ⟩
  ⟨,⟩-resp {A} {B} f≈f′ g≈g′
      = Bld.factorizer-resp (A ×′ B) (Bool-elim f≈f′ g≈g′)


  ⟨,⟩-projl : ∀ {A B Z} {f : Z ⇒ A} {g : Z ⇒ B} → projl ∘ ⟨ f , g ⟩ ≈ f
  ⟨,⟩-projl {A} {B} = Bld.factorizer-proj (A ×′ B)


  ⟨,⟩-projr : ∀ {A B Z} {f : Z ⇒ A} {g : Z ⇒ B} → projr ∘ ⟨ f , g ⟩ ≈ g
  ⟨,⟩-projr {A} {B} = Bld.factorizer-proj (A ×′ B)


  ⟨,⟩-unique : ∀ {A B Z} {f : Z ⇒ A} {g : Z ⇒ B} {u}
    → f ≈ projl ∘ u
    → g ≈ projr ∘ u
    → ⟨ f , g ⟩ ≈ u
  ⟨,⟩-unique {A} {B} eql eqr
    = Bld.factorizer-unique (A ×′ B) _ (Bool-elim eql eqr)


  ⟨,⟩-∘ : ∀ {A B Y Z} {f : Y ⇒ Z} {g : Z ⇒ A} {h : Z ⇒ B}
    → ⟨ g , h ⟩ ∘ f ≈ ⟨ g ∘ f , h ∘ f ⟩
  ⟨,⟩-∘ {A} {B} {Y} {Z} {f} {g} {h}
      = begin
          ⟨ g , h ⟩ ∘ f
        ≈⟨ Bld.factorizer-∘ (A ×′ B) ⟩
          Bld.factorizer (A ×′ B)
            (λ i → Bool-elim {A = λ i → Z ⇒ Bool-elim A B i} g h i ∘ f)
        ≈⟨ Bld.factorizer-resp (A ×′ B) (Bool-elim ≈.refl ≈.refl) ⟩
          ⟨ g ∘ f , h ∘ f ⟩
        ∎


  ⟨,⟩-id : ∀ {A B} → ⟨ projl , projr ⟩ ≈ id {A × B}
  ⟨,⟩-id {A} {B} = ⟨,⟩-unique (≈.sym id-r) (≈.sym id-r)


  ⟨×⟩-resp : ∀ {A A′ B B′} {f f′ : A ⇒ A′} {g g′ : B ⇒ B′}
    → f ≈ f′
    → g ≈ g′
    → ⟨ f × g ⟩ ≈ ⟨ f′ × g′ ⟩
  ⟨×⟩-resp {A} {A′} {B} {B′} f≈f′ g≈g′
      = Bld.times-resp (A ×′ B) (A′ ×′ B′) (Bool-elim f≈f′ g≈g′)


  ⟨×⟩-projl : ∀ {A A′ B B′} {f : A ⇒ A′} {g : B ⇒ B′}
    → projl ∘ ⟨ f × g ⟩ ≈ f ∘ projl
  ⟨×⟩-projl {A} {A′} {B} {B′} = Bld.times-proj (A ×′ B) (A′ ×′ B′)


  ⟨×⟩-projr : ∀ {A A′ B B′} {f : A ⇒ A′} {g : B ⇒ B′}
    → projr ∘ ⟨ f × g ⟩ ≈ g ∘ projr
  ⟨×⟩-projr {A} {A′} {B} {B′} = Bld.times-proj (A ×′ B) (A′ ×′ B′)


  ⟨×⟩-id : ∀ {A B} → ⟨ id {A} × id {B} ⟩ ≈ id
  ⟨×⟩-id {A} {B} = Bld.factorizer-unique (A ×′ B) id
    (Bool-elim (≈.trans id-l (≈.sym id-r)) (≈.trans id-l (≈.sym id-r)))


  ⟨×⟩-∘ : ∀ {A A′ A″ B B′ B″}
    → {f : A′ ⇒ A″} {f′ : A ⇒ A′} {g : B′ ⇒ B″} {g′ : B ⇒ B′}
    → ⟨ f × g ⟩ ∘ ⟨ f′ × g′ ⟩ ≈ ⟨ f ∘ f′ × g ∘ g′ ⟩
  ⟨×⟩-∘ {A} {A′} {A″} {B} {B′} {B″} {f} {f′} {g} {g′} = ≈.trans
    (Bld.times-∘ (A ×′ B) (A′ ×′ B′) (A″ ×′ B″))
    (Bld.times-resp (A ×′ B) (A″ ×′ B″) (Bool-elim ≈.refl ≈.refl))


  ⟨×⟩-⟨,⟩ : ∀ {A B C B′ C′} {f : A ⇒ B} {g : A ⇒ C} {f′ : B ⇒ B′} {g′ : C ⇒ C′}
    → ⟨ f′ × g′ ⟩ ∘ ⟨ f , g ⟩ ≈ ⟨ f′ ∘ f , g′ ∘ g ⟩
  ⟨×⟩-⟨,⟩ {A} {B} {C} {B′} {C′} = ≈.trans
    (Bld.times-factorizer (B ×′ C) (B′ ×′ C′))
    (Bld.factorizer-resp (B′ ×′ C′) (Bool-elim ≈.refl ≈.refl))


-- The following is conceptually trivial, but we have to dig quite deep to
-- avoid level-related nonsense.
HasProducts→HasBinaryProducts : ∀ {lp lo la l≈} {C : Category lo la l≈}
  → HasProducts lp C
  → HasBinaryProducts C
HasProducts→HasBinaryProducts {lp} {C = C} record { Π′ = Π }
    = record { _×′_ = _×_ }
  where
    open Category C
    open Unique.Build C
    open Product using (proj)
    open ∃!′ using (arr ; prop ; unique)

    _×_ : ∀ A B → Build.BinaryProduct C A B
    A × B = record
        { prod = prod′
        ; proj = proj′
        ; isProduct = isProduct′
        }
      where
        O : Lift lp Bool → _
        O (lift true) = A
        O (lift false) = B

        prod′ = Product.prod (Π O)

        proj′ = Bool-elim (proj (Π O) (lift true)) (proj (Π O) (lift false))

        isProduct′ : IsProduct C (Bool-elim A B) prod′ proj′
        isProduct′ {X} x = record
            { arr = arr′ ⃗
            ; prop = Bool-elim (prop arr′ (lift true)) (prop arr′ (lift false))
            ; unique = λ eq → unique arr′
                (λ { (lift true) → eq true ; (lift false) → eq false})
            }
          where
            arr′ = Product.isProduct (Π O)
              λ { (lift true) → x true ; (lift false) → x false}



record HasFiniteProducts {lo la l≈} (Cat : Category lo la l≈)
  : Set (lo ⊔ la ⊔ l≈)
  where

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
