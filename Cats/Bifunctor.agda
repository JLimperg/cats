module Cats.Bifunctor where

open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence ; _Preserves₂_⟶_⟶_)

open import Cats.Category
open import Cats.Category.Cat using (_∘_ ; ∘-resp ; _≈_ ; equiv)
open import Cats.Category.Cat.Facts.Product using (Swap ; hasBinaryProducts)
open import Cats.Category.Fun using (Fun ; Trans ; ≈-intro ; ≈-elim)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Category.Product.Binary.Facts using (iso-intro)
open import Cats.Functor using (Functor)
open import Cats.Trans.Iso using (NatIso)
open import Cats.Util.Simp using (simp!)

import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Fun.Facts as Fun

open Functor
open Trans
open Iso.Build._≅_


module _ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″} where

  Bifunctor
    : Category lo la l≈
    → Category lo′ la′ l≈′
    → Category lo″ la″ l≈″
    → Set (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′ ⊔ lo″ ⊔ la″ ⊔ l≈″)
  Bifunctor C D E = Functor (C × D) E


  module _
    {C : Category lo la l≈}
    {D : Category lo′ la′ l≈′}
    {E : Category lo″ la″ l≈″}
    where

    private
      module C = Category C
      module D = Category D
      module E = Category E


    biobj : Bifunctor C D E → C.Obj → D.Obj → E.Obj
    biobj F c d = fobj F (c , d)


    bimap
      : (F : Bifunctor C D E)
      → ∀ {A B A′ B′}
      → (A C.⇒ B)
      → (A′ D.⇒ B′)
      → biobj F A A′ E.⇒ biobj F B B′
    bimap F f g = fmap F (f , g)


    Bifunctor→Functor₁ : Bifunctor C D E → C.Obj → Functor D E
    Bifunctor→Functor₁ F x = record
        { fobj = λ d → fobj F (x , d)
        ; fmap = λ f → fmap F (C.id , f)
        ; fmap-resp = λ x≈y → fmap-resp F (C.≈.refl , x≈y)
        ; fmap-id = fmap-id F
        ; fmap-∘ = λ where
            {f = f} {g} →
              begin
                fmap F (C.id , f) E.∘ fmap F (C.id , g)
              ≈⟨ fmap-∘ F ⟩
                fmap F (C.id C.∘ C.id , f D.∘ g)
              ≈⟨ fmap-resp F (C.id-l , D.≈.refl) ⟩
                fmap F (C.id , f D.∘ g)
              ∎
        }
      where
        open E.≈-Reasoning


    Bifunctor→Functor₁-resp : ∀ {F G x y}
      → F ≈ G
      → x C.≅ y
      → Bifunctor→Functor₁ F x ≈ Bifunctor→Functor₁ G y
    Bifunctor→Functor₁-resp {F} {G} {x} {y}
      record { iso = Fx≅Gx ; forth-natural = fnat } x≅y
        = record
        { iso = λ {z} →
            let open E.≅-Reasoning in
            begin
              fobj F (x , z)
            ≈⟨ Fx≅Gx ⟩
              fobj G (x , z)
            ≈⟨ fobj-resp G (iso-intro x≅y D.≅.refl) ⟩
              fobj G (y , z)
            ∎
        ; forth-natural = λ {c} {d} {f} →
            let open E.≈-Reasoning in
            triangle (fmap G (forth x≅y , f) E.∘ forth Fx≅Gx)
            ( begin
                ((E.id E.∘ fmap G (forth x≅y , D.id)) E.∘ forth Fx≅Gx) E.∘ fmap F (C.id , f)
              ≈⟨ simp! E ⟩
                fmap G (forth x≅y , D.id) E.∘ forth Fx≅Gx E.∘ fmap F (C.id , f)
              ≈⟨ E.∘-resp-r fnat ⟩
                fmap G (forth x≅y , D.id) E.∘ (fmap G (C.id , f) E.∘ forth Fx≅Gx)
              ≈⟨ simp! E ⟩
                (fmap G (forth x≅y , D.id) E.∘ fmap G (C.id , f)) E.∘ forth Fx≅Gx
              ≈⟨ E.∘-resp-l (fmap-∘ G) ⟩
                fmap G (forth x≅y C.∘ C.id , D.id D.∘ f) E.∘ forth Fx≅Gx
              ≈⟨ E.∘-resp-l (fmap-resp G (C.id-r , D.id-l)) ⟩
                fmap G (forth x≅y , f) E.∘ forth Fx≅Gx
              ∎
            )
            ( begin
                fmap G (C.id , f) E.∘ (E.id E.∘ fmap G (forth x≅y , D.id)) E.∘ forth Fx≅Gx
              ≈⟨ E.∘-resp-r (E.∘-resp-l E.id-l) ⟩
                fmap G (C.id , f) E.∘ fmap G (forth x≅y , D.id) E.∘ forth Fx≅Gx
              ≈⟨ simp! E ⟩
                (fmap G (C.id , f) E.∘ fmap G (forth x≅y , D.id)) E.∘ forth Fx≅Gx
              ≈⟨ E.∘-resp-l (fmap-∘ G) ⟩
                fmap G (C.id C.∘ forth x≅y , f D.∘ D.id) E.∘ forth Fx≅Gx
              ≈⟨ E.∘-resp-l (fmap-resp G (C.id-l , D.id-r)) ⟩
                fmap G (forth x≅y , f) E.∘ forth Fx≅Gx
              ∎
            )
        }


    transposeBifunctor₁ : Bifunctor C D E → Functor C (Fun D E)
    transposeBifunctor₁ F = record
        { fobj = Bifunctor→Functor₁ F
        ; fmap = λ {a} {b} f → record
            { component = λ d → fmap F (f , D.id)
            ; natural = λ {a′} {b′} {g} →
                begin
                  fmap F (f , D.id) E.∘ fmap (Bifunctor→Functor₁ F a) g
                ≈⟨ fmap-∘ F ⟩
                  fmap F (f C.∘ C.id , D.id D.∘ g)
                ≈⟨ fmap-resp F
                    ( (C.≈.trans C.id-r (C.≈.sym C.id-l))
                    , D.≈.trans D.id-l (D.≈.sym D.id-r) ) ⟩
                  fmap F (C.id C.∘ f , g D.∘ D.id)
                ≈⟨ E.≈.sym (fmap-∘ F) ⟩
                  fmap (Bifunctor→Functor₁ F b) g E.∘ fmap F (f , D.id)
                ∎
            }
        ; fmap-resp = λ x≈y → ≈-intro (fmap-resp F (x≈y , D.≈.refl))
        ; fmap-id = ≈-intro (fmap-id F)
        ; fmap-∘ = λ where
            {f = f} {g} → ≈-intro (
              begin
                fmap F (f , D.id) E.∘ fmap F (g , D.id)
              ≈⟨ fmap-∘ F ⟩
                fmap F (f C.∘ g , D.id D.∘ D.id)
              ≈⟨ fmap-resp F (C.≈.refl , D.id-l) ⟩
                fmap F (f C.∘ g , D.id)
              ∎)
        }
      where
        open E.≈-Reasoning


    transposeBifunctor₁-resp : ∀ {F G}
      → F ≈ G
      → transposeBifunctor₁ F ≈ transposeBifunctor₁ G
    transposeBifunctor₁-resp {F} {G} F≈G = record
        { iso = Fun.≈→≅ (Bifunctor→Functor₁-resp F≈G C.≅.refl)
        ; forth-natural = λ {c} {d} {f} → ≈-intro (
            let open E.≈-Reasoning in
            triangle (fmap G (f , D.id) E.∘ forth (iso F≈G))
            ( begin
                ((E.id E.∘ fmap G (C.id , D.id)) E.∘ forth (iso F≈G)) E.∘ fmap F (f , D.id)
              ≈⟨ E.∘-resp-l (E.≈.trans (E.∘-resp-l (E.≈.trans E.id-l (fmap-id G))) E.id-l) ⟩
                forth (iso F≈G) E.∘ fmap F (f , D.id)
              ≈⟨ forth-natural F≈G ⟩
                (fmap G (f , D.id) E.∘ forth (iso F≈G))
              ∎
            )
            ( begin
                fmap G (f , D.id) E.∘ (E.id E.∘ fmap G (C.id , D.id)) E.∘ forth (iso F≈G)
              ≈⟨ E.∘-resp-r (E.≈.trans (E.∘-resp-l (E.≈.trans E.id-l (fmap-id G))) E.id-l) ⟩
                fmap G (f , D.id) E.∘ forth (iso F≈G)
              ∎
            ))
        }
      where
        open E.≈-Reasoning
        open NatIso using (iso ; forth-natural)


module _
  {lo la l≈} {C : Category lo la l≈}
  {lo′ la′ l≈′} {D : Category lo′ la′ l≈′}
  {lo″ la″ l≈″} {E : Category lo″ la″ l≈″}
  where

  private
    module C = Category C
    module D = Category D
    module E = Category E


  Bifunctor→Functor₂ : Bifunctor C D E → D.Obj → Functor C E
  Bifunctor→Functor₂ F x = Bifunctor→Functor₁ (F ∘ Swap) x


  Bifunctor→Functor₂-resp : ∀ {F G x y}
    → F ≈ G
    → x D.≅ y
    → Bifunctor→Functor₂ F x ≈ Bifunctor→Functor₂ G y
  Bifunctor→Functor₂-resp {F} {G} F≈G x≅y
      = Bifunctor→Functor₁-resp {F = F ∘ Swap} {G = G ∘ Swap} (∘-resp F≈G refl) x≅y
    where
      open IsEquivalence equiv


  transposeBifunctor₂ : Bifunctor C D E → Functor D (Fun C E)
  transposeBifunctor₂ F = transposeBifunctor₁ (F ∘ Swap)


  transposeBifunctor₂-resp : ∀ {F G}
    → F ≈ G → transposeBifunctor₂ F ≈ transposeBifunctor₂ G
  transposeBifunctor₂-resp {F} {G} F≈G
      = transposeBifunctor₁-resp {F = F ∘ Swap} {G = G ∘ Swap} (∘-resp F≈G refl)
    where
      open IsEquivalence equiv
