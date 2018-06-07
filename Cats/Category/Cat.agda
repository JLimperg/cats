module Cats.Category.Cat where

open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)
open import Level
open import Relation.Binary using
  (IsEquivalence ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Category
open import Cats.Category.Zero
open import Cats.Category.One
open import Cats.Functor using (Functor ; _∘_ ; id)
open import Cats.Util.Assoc using (assoc!)


module Build where

  _⇒_ : ∀ {lo la l≈ lo′ la′ l≈′}
    → Category lo la l≈ → Category lo′ la′ l≈′ → Set _
  C ⇒ D = Functor C D


  module _ lo la l≈ where

    infixr 4 _≈_


    Obj : Set (suc (lo ⊔ la ⊔ l≈))
    Obj = Category lo la l≈


    record _≈_ {C D : Obj} (F G : C ⇒ D) : Set (lo ⊔ la ⊔ l≈) where
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


    equiv : ∀ {C D} → IsEquivalence (_≈_ {C = C} {D})
    equiv {C} {D} = record
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
            ; fmap-≈ = λ _ → ≈.trans (≈.sym D.id-r) (≈.sym D.id-l)
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
                  ≈⟨ D.∘-resp-r (D.∘-resp-l (fmap-≈-FG f)) ⟩
                    forth F≅G D.∘ (back F≅G D.∘ G.fmap f D.∘ forth F≅G) D.∘ back F≅G
                  ≈⟨ assoc! D ⟩
                    (forth F≅G D.∘ back F≅G) D.∘ G.fmap f D.∘ forth F≅G D.∘ back F≅G
                  ≈⟨ D.∘-resp-l (forth-back F≅G) ⟩
                    D.id D.∘ G.fmap f D.∘ forth F≅G D.∘ back F≅G
                  ≈⟨ D.id-l ⟩
                    G.fmap f D.∘ forth F≅G D.∘ back F≅G
                  ≈⟨ D.∘-resp-r (forth-back F≅G) ⟩
                    G.fmap f D.∘ D.id
                  ≈⟨ D.id-r ⟩
                    G.fmap f
                  ∎
                )

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
                  ≈⟨ assoc! D ⟩
                    back F≅G D.∘ (back G≅H D.∘ H.fmap f D.∘ forth G≅H) D.∘ forth F≅G
                  ≈⟨ D.∘-resp-r (D.∘-resp-l (≈.sym (fmap-≈-GH f))) ⟩
                    back F≅G D.∘ G.fmap f D.∘ forth F≅G
                  ≈⟨ ≈.sym (fmap-≈-FG f) ⟩
                    F.fmap f
                  ∎
                )


    ∘-resp : ∀ {C D E : Obj} → _∘_ {C = C} {D} {E} Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    ∘-resp {C} {D} {E} {F} {G} {H} {I}
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
              ≈⟨ assoc! E ⟩
                back F≅G E.∘ (G.fmap (back H≅I) E.∘ G.fmap (I.fmap f) E.∘ G.fmap (forth H≅I)) E.∘ forth F≅G
              ≈⟨ E.∘-resp-r (E.∘-resp-l (≈.trans (E.∘-resp-r (≈.sym (G.fmap-∘ _ _))) (≈.sym (G.fmap-∘ _ _)))) ⟩
                back F≅G E.∘ G.fmap (back H≅I D.∘ I.fmap f D.∘ forth H≅I) E.∘ forth F≅G
              ≈⟨ E.∘-resp-r (E.∘-resp-l (G.fmap-resp (D.≈.sym (fmap-≈-HI _)))) ⟩
                back F≅G E.∘ G.fmap (H.fmap f) E.∘ forth F≅G
              ≈⟨ ≈.sym (fmap-≈-FG _) ⟩
                F.fmap (H.fmap f)
              ∎
            )


    id-r : {C D : Obj} → {F : C ⇒ D} → F ∘ id ≈ F
    id-r {C} {D} {F} = record
        { iso = D.≅.refl
        ; fmap-≈ = λ _ → D.≈.sym (D.≈.trans D.id-l D.id-r)
        }
      where
        module D = Category D


    id-l : {C D : Obj} → {F : C ⇒ D} → id ∘ F ≈ F
    id-l {C} {D} {F} = record
        { iso = D.≅.refl
        ; fmap-≈ = λ _ → D.≈.sym (D.≈.trans D.id-l D.id-r)
        }
      where
        module D = Category D


    assoc : ∀ {B C D E : Obj} (F : D ⇒ E) (G : C ⇒ D) (H : B ⇒ C)
      → (F ∘ G) ∘ H ≈ F ∘ (G ∘ H)
    assoc {B} {C} {D} {E} _ _ _ = record
        { iso = E.≅.refl
        ; fmap-≈ = λ _ → E.≈.sym (E.≈.trans E.id-l E.id-r)
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
        ; equiv = equiv
        ; ∘-resp = ∘-resp
        ; id-r = id-r
        ; id-l = id-l
        ; assoc = λ {_} {_} {_} {_} {F} {G} {H} → assoc F G H
        }


open Build public using (Cat)
