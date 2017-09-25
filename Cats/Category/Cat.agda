module Cats.Category.Cat where

open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)
open import Level
open import Relation.Binary using (IsEquivalence ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Category
open import Cats.Category.Zero
open import Cats.Category.One
open import Cats.Functor
open import Cats.Util.Assoc using (assoc!)


module _ lo la l≈ where

  infixr 9 _∘_
  infixr 4 _≈_


  Obj : Set (suc (lo ⊔ la ⊔ l≈))
  Obj = Category lo la l≈

  _⇒_ : Obj → Obj → Set (lo ⊔ la ⊔ l≈)
  C ⇒ D = Functor C D


  id : {C : Obj} → C ⇒ C
  id {C} = record
      { fobj = λ x → x
      ; fmap = λ f → f
      ; fmap-preserves-≈ = λ eq → eq
      ; id-preservation = C.≈.reflexive ≡.refl
      ; ∘-commut = λ _ _ → C.≈.reflexive ≡.refl
      }
    where
      module C = Category C


  _∘_ : ∀ {C D E} → D ⇒ E → C ⇒ D → C ⇒ E
  _∘_ {C} {D} {E} F G = record
      { fobj = fobj
      ; fmap = fmap
      ; fmap-preserves-≈ = fmap-preserves-≈
      ; id-preservation = id-preservation
      ; ∘-commut = ∘-commut
      }
    where
      module F = Functor F
      module G = Functor G
      module C = Category C
      module E = Category E
      module ≈ = E.≈

      fobj : C.Obj → E.Obj
      fobj = λ x → F.fobj (G.fobj x)

      fmap : ∀ {A B} → A C.⇒ B → fobj A E.⇒ fobj B
      fmap = λ f → F.fmap (G.fmap f)

      fmap-preserves-≈ : ∀ {A B} → fmap {A} {B} Preserves C._≈_ ⟶ E._≈_
      fmap-preserves-≈ eq = F.fmap-preserves-≈ (G.fmap-preserves-≈ eq)

      id-preservation : ∀ {A} → F.fmap (G.fmap (C.id {A})) E.≈ E.id
      id-preservation
          = ≈.trans (F.fmap-preserves-≈ G.id-preservation) F.id-preservation

      ∘-commut : ∀ {A B C} (f : B C.⇒ C) (g : A C.⇒ B)
        → fmap (f C.∘ g) E.≈ fmap f E.∘ fmap g
      ∘-commut f g
          = ≈.trans (F.fmap-preserves-≈ (G.∘-commut _ _)) (F.∘-commut _ _)


  record _≈_ {C D} (F G : C ⇒ D) : Set (lo ⊔ la ⊔ l≈) where
    private
      module C = Category C
      module D = Category D
      module F = Functor F
      module G = Functor G

    field
      iso : ∀ {x} → F.fobj x D.≅ G.fobj x

    open D._≅_

    field
      fmap-≈ : ∀ {A B} (f : A C.⇒ B)
        → F.fmap f D.≈ back iso D.∘ G.fmap f D.∘ forth iso


  ≈-equiv : ∀ {C D} → IsEquivalence (_≈_ {C = C} {D})
  ≈-equiv {C} {D} = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    where
      module C = Category C
      module D = Category D
      module ≈ = D.≈
      open Category._≅_

      refl : ∀ {F : C ⇒ D} → F ≈ F
      refl = record
          { iso = D.≅.refl
          ; fmap-≈ = λ _ →
              ≈.trans (≈.sym D.id-identity-r) (≈.sym D.id-identity-l)
          }

      sym : ∀ {F G : C ⇒ D} → F ≈ G → G ≈ F
      sym {F} {G} record { iso = F≅G ; fmap-≈ = fmap-≈-FG } = record
          { iso = iso
          ; fmap-≈ = fmap-≈
          }
        where
          module F = Functor F
          module G = Functor G

          iso : ∀ {x} → G.fobj x D.≅ F.fobj x
          iso = D.≅.sym F≅G

          open D.≈-Reasoning

          fmap-≈ : ∀ {A B} (f : A C.⇒ B)
            → G.fmap f D.≈ back iso D.∘ F.fmap f D.∘ forth iso
          fmap-≈ f
              = ≈.sym
              ( begin
                  back iso D.∘ F.fmap f D.∘ forth iso
                ≈⟨ D.∘-preserves-≈ ≈.refl (D.∘-preserves-≈ (fmap-≈-FG f) ≈.refl) ⟩
                  forth F≅G D.∘ (back F≅G D.∘ G.fmap f D.∘ forth F≅G) D.∘ back F≅G
                ≈⟨ lem ⟩
                  (forth F≅G D.∘ back F≅G) D.∘ G.fmap f D.∘ forth F≅G D.∘ back F≅G
                ≈⟨ D.∘-preserves-≈ (forth-back F≅G) ≈.refl ⟩
                  D.id D.∘ G.fmap f D.∘ forth F≅G D.∘ back F≅G
                ≈⟨ D.id-identity-l ⟩
                  G.fmap f D.∘ forth F≅G D.∘ back F≅G
                ≈⟨ D.∘-preserves-≈ ≈.refl (forth-back F≅G) ⟩
                  G.fmap f D.∘ D.id
                ≈⟨ D.id-identity-r ⟩
                  G.fmap f
                ∎
              )
            where
              module F≅G {x} = Category._≅_ (F≅G {x})
              lem : forth F≅G D.∘ (back F≅G D.∘ G.fmap f D.∘ forth F≅G) D.∘ back F≅G D.≈
                    (forth F≅G D.∘ back F≅G) D.∘ G.fmap f D.∘ forth F≅G D.∘ back F≅G
              lem = assoc! D

      trans : ∀ {F G H : C ⇒ D} → F ≈ G → G ≈ H → F ≈ H
      trans {F} {G} {H}
        record { iso = F≅G ; fmap-≈ = fmap-≈-FG }
        record { iso = G≅H ; fmap-≈ = fmap-≈-GH }
          = record
          { iso = iso
          ; fmap-≈ = fmap-≈
          }
        where
          module F = Functor F
          module G = Functor G
          module H = Functor H

          iso : ∀ {x} → F.fobj x D.≅ H.fobj x
          iso = D.≅.trans F≅G G≅H

          open D.≈-Reasoning

          fmap-≈ : ∀ {A B} (f : A C.⇒ B)
            → F.fmap f D.≈ back iso D.∘ H.fmap f D.∘ forth iso
          fmap-≈ f
              = ≈.sym
              ( begin
                  back iso D.∘ H.fmap f D.∘ forth iso
                ≡⟨ ≡.refl ⟩
                  (back F≅G D.∘ back G≅H) D.∘ H.fmap f D.∘ forth G≅H D.∘ forth F≅G
                ≈⟨ lem ⟩
                  back F≅G D.∘ (back G≅H D.∘ H.fmap f D.∘ forth G≅H) D.∘ forth F≅G
                ≈⟨ D.∘-preserves-≈ ≈.refl (D.∘-preserves-≈ (≈.sym (fmap-≈-GH f)) ≈.refl) ⟩
                  back F≅G D.∘ G.fmap f D.∘ forth F≅G
                ≈⟨ ≈.sym (fmap-≈-FG f) ⟩
                  F.fmap f
                ∎
              )
            where
              lem : (back F≅G D.∘ back G≅H) D.∘ H.fmap f D.∘ forth G≅H D.∘ forth F≅G D.≈
                    back F≅G D.∘ (back G≅H D.∘ H.fmap f D.∘ forth G≅H) D.∘ forth F≅G
              lem = assoc! D


  ∘-preserves-≈ : ∀ {C D E} → _∘_ {C} {D} {E} Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ∘-preserves-≈ {C} {D} {E} {F} {G} {H} {I}
    record { iso = F≅G ; fmap-≈ = fmap-≈-FG }
    record { iso = H≅I ; fmap-≈ = fmap-≈-HI }
      = record
      { iso = iso
      ; fmap-≈ = fmap-≈
      }
    where
      module C = Category C
      module D = Category D
      module E = Category E
      module F = Functor F
      module G = Functor G
      module H = Functor H
      module I = Functor I

      iso : ∀ {x} → F.fobj (H.fobj x) E.≅ G.fobj (I.fobj x)
      iso {x} = E.≅.trans F≅G (G.fobj-preserves-≅ H≅I)


      open Category._≅_
      open E.≈-Reasoning
      module ≈ = E.≈

      fmap-≈ : ∀ {A B} (f : A C.⇒ B)
        → F.fmap (H.fmap f) E.≈ back iso E.∘ G.fmap (I.fmap f) E.∘ forth iso
      fmap-≈ f
          = ≈.sym
          ( begin
              back iso E.∘ G.fmap (I.fmap f) E.∘ forth iso
            ≡⟨ ≡.refl ⟩
              (back F≅G E.∘ G.fmap (back H≅I)) E.∘ G.fmap (I.fmap f) E.∘ (G.fmap (forth H≅I) E.∘ forth F≅G)
            ≈⟨ lem ⟩
              back F≅G E.∘ (G.fmap (back H≅I) E.∘ G.fmap (I.fmap f) E.∘ G.fmap (forth H≅I)) E.∘ forth F≅G
            ≈⟨ E.∘-preserves-≈ ≈.refl (E.∘-preserves-≈ (≈.trans (E.∘-preserves-≈ ≈.refl (≈.sym (G.∘-commut _ _))) (≈.sym (G.∘-commut _ _))) ≈.refl) ⟩
              back F≅G E.∘ G.fmap (back H≅I D.∘ I.fmap f D.∘ forth H≅I) E.∘ forth F≅G
            ≈⟨ E.∘-preserves-≈ ≈.refl (E.∘-preserves-≈ (G.fmap-preserves-≈ (D.≈.sym (fmap-≈-HI _))) ≈.refl) ⟩
              back F≅G E.∘ G.fmap (H.fmap f) E.∘ forth F≅G
            ≈⟨ ≈.sym (fmap-≈-FG _) ⟩
              F.fmap (H.fmap f)
            ∎
          )
        where
          lem : (back F≅G E.∘ G.fmap (back H≅I)) E.∘ G.fmap (I.fmap f) E.∘ (G.fmap (forth H≅I) E.∘ forth F≅G) E.≈
                back F≅G E.∘ (G.fmap (back H≅I) E.∘ G.fmap (I.fmap f) E.∘ G.fmap (forth H≅I)) E.∘ forth F≅G
          lem = assoc! E

  id-identity-r : ∀ {C D} {F : C ⇒ D} → F ∘ id ≈ F
  id-identity-r {C} {D} {F} = record
      { iso = D.≅.refl
      ; fmap-≈ = λ _ → D.≈.sym (D.≈.trans D.id-identity-l D.id-identity-r)
      }
    where
      module D = Category D


  id-identity-l : ∀ {C D} {F : C ⇒ D} → id ∘ F ≈ F
  id-identity-l {C} {D} {F} = record
      { iso = D.≅.refl
      ; fmap-≈ = λ _ → D.≈.sym (D.≈.trans D.id-identity-l D.id-identity-r)
      }
    where
      module D = Category D


  ∘-assoc : ∀ {B C D E} (F : D ⇒ E) (G : C ⇒ D) (H : B ⇒ C)
    → (F ∘ G) ∘ H ≈ F ∘ (G ∘ H)
  ∘-assoc {B} {C} {D} {E} F G H = record
      { iso = E.≅.refl
      ; fmap-≈ = λ _ → E.≈.sym (E.≈.trans E.id-identity-l E.id-identity-r)
      }
    where
      module E = Category E


  instance Cat : Category (suc (lo ⊔ la ⊔ l≈)) (lo ⊔ la ⊔ l≈) (lo ⊔ la ⊔ l≈)
  Cat = record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = _∘_
      ; ≈-equiv = ≈-equiv
      ; ∘-preserves-≈ = ∘-preserves-≈
      ; id-identity-r = id-identity-r
      ; id-identity-l = id-identity-l
      ; ∘-assoc = ∘-assoc
      }


-- TODO more universe polymorphism for Zero and One
Zero-Initial : IsInitial {{C = Cat zero zero zero}} Zero
Zero-Initial X = f , f-Unique
  where
    f : Functor Zero X
    f = record
        { fobj = λ()
        ; fmap = λ{}
        ; fmap-preserves-≈ = λ{}
        ; id-preservation = λ{}
        ; ∘-commut = λ{}
        }

    f-Unique : IsUnique f
    f-Unique f′ = record
        { iso = λ{}
        ; fmap-≈ = λ{}
        }


One-Terminal : IsTerminal {{C = Cat zero zero zero}} One
One-Terminal X = f , f-Unique
  where
    f : Functor X One
    f = record
        { fobj = λ x → tt
        ; fmap = λ _ → tt
        ; fmap-preserves-≈ = λ _ → tt
        ; id-preservation = tt
        ; ∘-commut = λ _ _ → tt
        }

    f-Unique : IsUnique f
    f-Unique f′ = record
        { iso = record
            { forth = tt
            ; back = tt
            ; back-forth = tt
            ; forth-back = tt
            }
        ; fmap-≈ = λ _ → tt
        }
