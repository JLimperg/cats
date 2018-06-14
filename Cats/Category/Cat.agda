module Cats.Category.Cat where

open import Cats.Functor public using (Functor ; _∘_ ; id)

open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)
open import Level
open import Relation.Binary using
  (IsEquivalence ; _Preserves_⟶_ ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Category
open import Cats.Category.Zero
open import Cats.Category.One
open import Cats.Util.Assoc using (assoc!)


_⇒_ : ∀ {lo la l≈ lo′ la′ l≈′}
  → Category lo la l≈ → Category lo′ la′ l≈′ → Set _
C ⇒ D = Functor C D


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  infixr 4 _≈_


  record _≈_ (F G : C ⇒ D) : Set (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′) where
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


  equiv : IsEquivalence _≈_
  equiv = record
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


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  ∘-resp : ∀ {lo″ la″ l≈″} {E : Category lo″ la″ l≈″}
    → {F G : D ⇒ E} {H I : C ⇒ D}
    → F ≈ G
    → H ≈ I
    → F ∘ H ≈ G ∘ I
  ∘-resp {E = E} {F} {G} {H} {I}
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
      iso {x} = E.≅.trans F≅G (G.fobj-resp H≅I)


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
            ≈⟨ E.∘-resp-r (E.∘-resp-l (≈.trans (E.∘-resp-r (G.fmap-∘ )) (G.fmap-∘ ))) ⟩
              back F≅G E.∘ G.fmap (back H≅I D.∘ I.fmap f D.∘ forth H≅I) E.∘ forth F≅G
            ≈⟨ E.∘-resp-r (E.∘-resp-l (G.fmap-resp (D.≈.sym (fmap-≈-HI _)))) ⟩
              back F≅G E.∘ G.fmap (H.fmap f) E.∘ forth F≅G
            ≈⟨ ≈.sym (fmap-≈-FG _) ⟩
              F.fmap (H.fmap f)
            ∎
          )


  id-r : {F : C ⇒ D} → F ∘ id ≈ F
  id-r {F} = record
      { iso = D.≅.refl
      ; fmap-≈ = λ _ → D.≈.sym (D.≈.trans D.id-l D.id-r)
      }
    where
      module D = Category D


  id-l : {F : C ⇒ D} → id ∘ F ≈ F
  id-l {F} = record
      { iso = D.≅.refl
      ; fmap-≈ = λ _ → D.≈.sym (D.≈.trans D.id-l D.id-r)
      }
    where
      module D = Category D


  assoc : ∀ {lo″ la″ l≈″ lo‴ la‴ l≈‴}
    → {E : Category lo″ la″ l≈″} {X : Category lo‴ la‴ l≈‴}
    → (F : E ⇒ X) (G : D ⇒ E) (H : C ⇒ D)
    → (F ∘ G) ∘ H ≈ F ∘ (G ∘ H)
  assoc {E = E} {X} _ _ _ = record
      { iso = X.≅.refl
      ; fmap-≈ = λ _ → X.≈.sym (X.≈.trans X.id-l X.id-r)
      }
    where
      module X = Category X


instance
  Cat : ∀ lo la l≈
    → Category (suc (lo ⊔ la ⊔ l≈)) (lo ⊔ la ⊔ l≈) (lo ⊔ la ⊔ l≈)
  Cat lo la l≈ = record
      { Obj = Category lo la l≈
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
