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
open import Cats.Trans.Iso as NatIso using (NatIso ; iso ; forth-natural)
open import Cats.Util.Simp using (simp!)

open Functor
open Category._≅_


_⇒_ : ∀ {lo la l≈ lo′ la′ l≈′}
  → Category lo la l≈ → Category lo′ la′ l≈′ → Set _
C ⇒ D = Functor C D


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  infixr 4 _≈_


  _≈_ : (F G : C ⇒ D) → Set (lo ⊔ la ⊔ lo′ ⊔ la′ ⊔ l≈′)
  F ≈ G = NatIso F G


  equiv : IsEquivalence _≈_
  equiv = record
      { refl = NatIso.id
      ; sym = NatIso.sym
      ; trans = λ eq₁ eq₂ → eq₂ NatIso.∘ eq₁
      }


module _ {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  where

  ∘-resp : ∀ {lo″ la″ l≈″} {E : Category lo″ la″ l≈″}
    → {F G : D ⇒ E} {H I : C ⇒ D}
    → F ≈ G
    → H ≈ I
    → F ∘ H ≈ G ∘ I
  ∘-resp {E = E} {F} {G} {H} {I}
    record { iso = F≅G ; forth-natural = fnat-GH }
    record { iso = H≅I ; forth-natural = fnat-HI }
      = record
      { iso = E.≅.trans F≅G (fobj-resp G H≅I)
      ; forth-natural = λ {_} {_} {f} →
          begin
            (fmap G (forth H≅I) E.∘ forth F≅G) E.∘ fmap F (fmap H f)
          ≈⟨ simp! E ⟩
            fmap G (forth H≅I) E.∘ forth F≅G E.∘ fmap F (fmap H f)
          ≈⟨ E.∘-resp-r fnat-GH ⟩
            fmap G (forth H≅I) E.∘ fmap G (fmap H f) E.∘ forth F≅G
          ≈⟨ simp! E ⟩
            (fmap G (forth H≅I) E.∘ fmap G (fmap H f)) E.∘ forth F≅G
          ≈⟨ E.∘-resp-l (fmap-∘ G) ⟩
            fmap G (forth H≅I D.∘ fmap H f) E.∘ forth F≅G
          ≈⟨ E.∘-resp-l (fmap-resp G fnat-HI) ⟩
            fmap G (fmap I f D.∘ forth H≅I) E.∘ forth F≅G
          ≈⟨ E.∘-resp-l (E.≈.sym (fmap-∘ G)) ⟩
            (fmap G (fmap I f) E.∘ fmap G (forth H≅I)) E.∘ forth F≅G
          ≈⟨ simp! E ⟩
            fmap G (fmap I f) E.∘ fmap G (forth H≅I) E.∘ forth F≅G
          ∎
      }
    where
      module D = Category D
      module E = Category E
      open E.≈-Reasoning


  id-r : {F : C ⇒ D} → F ∘ id ≈ F
  id-r {F} = record
      { iso = D.≅.refl
      ; forth-natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
      }
    where
      module D = Category D


  id-l : {F : C ⇒ D} → id ∘ F ≈ F
  id-l {F} = record
      { iso = D.≅.refl
      ; forth-natural = D.≈.trans D.id-l (D.≈.sym D.id-r)
      }
    where
      module D = Category D


  assoc : ∀ {lo″ la″ l≈″ lo‴ la‴ l≈‴}
    → {E : Category lo″ la″ l≈″} {X : Category lo‴ la‴ l≈‴}
    → (F : E ⇒ X) (G : D ⇒ E) (H : C ⇒ D)
    → (F ∘ G) ∘ H ≈ F ∘ (G ∘ H)
  assoc {E = E} {X} _ _ _ = record
      { iso = X.≅.refl
      ; forth-natural = X.≈.trans X.id-l (X.≈.sym X.id-r)
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
