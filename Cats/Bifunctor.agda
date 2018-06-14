module Cats.Bifunctor where

open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)

open import Cats.Category
open import Cats.Category.Cat using (_≈_)
open import Cats.Category.Cat.Facts.Product using (hasBinaryProducts)
open import Cats.Category.Fun using (Fun ; Trans)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Category.Product.Binary.Facts using (iso-intro)
open import Cats.Functor using (Functor)
open import Cats.Util.Assoc using (assoc!)

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
      module D↝E = Category (Fun D E)
      open module HBP {lo} {la} {l≈} =
        HasBinaryProducts (hasBinaryProducts lo la l≈)


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
      record { iso = Fx≅Gx ; fmap-≈ = fmap-≈ } x≅y
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
        ; fmap-≈ = λ f →
            let open E.≈-Reasoning in
            E.≈.sym (
              begin
                (back Fx≅Gx E.∘ fmap G (back x≅y , D.id) E.∘ E.id) E.∘
                fmap G (C.id , f) E.∘
                (E.id E.∘ fmap G (forth x≅y , D.id)) E.∘ forth Fx≅Gx
              ≈⟨ E.∘-resp (E.∘-resp-r E.id-r) (E.∘-resp-r (E.∘-resp-l E.id-l)) ⟩
                (back Fx≅Gx E.∘ fmap G (back x≅y , D.id)) E.∘
                fmap G (C.id , f) E.∘
                fmap G (forth x≅y , D.id) E.∘ forth Fx≅Gx
              ≈⟨ assoc! E ⟩
                back Fx≅Gx E.∘ (fmap G (back x≅y , D.id) E.∘
                fmap G (C.id , f) E.∘
                fmap G (forth x≅y , D.id)) E.∘ forth Fx≅Gx
              ≈⟨ E.∘-resp-r (E.∘-resp-l
                   (E.≈.trans
                     (E.∘-resp-r (fmap-∘ G))
                     (fmap-∘ G))) ⟩
                back Fx≅Gx E.∘
                fmap G (back x≅y C.∘ C.id C.∘ forth x≅y , D.id D.∘ f D.∘ D.id) E.∘
                forth Fx≅Gx
              ≈⟨ E.≈.sym (fmap-≈ _) ⟩
                fmap F (back x≅y C.∘ C.id C.∘ forth x≅y , D.id D.∘ f D.∘ D.id)
              ≈⟨ fmap-resp F
                   ( (C.≈.trans (C.∘-resp-r C.id-l) (back-forth x≅y))
                   , D.≈.trans D.id-l D.id-r
                   ) ⟩
                fmap F (C.id , f)
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
        ; fmap-resp = λ x≈y d → fmap-resp F (x≈y , D.≈.refl)
        ; fmap-id = λ _ → fmap-id F
        ; fmap-∘ = λ where
            {f = f} {g} d →
              begin
                fmap F (f , D.id) E.∘ fmap F (g , D.id)
              ≈⟨ fmap-∘ F ⟩
                fmap F (f C.∘ g , D.id D.∘ D.id)
              ≈⟨ fmap-resp F (C.≈.refl , D.id-l) ⟩
                fmap F (f C.∘ g , D.id)
              ∎
        }
      where
        open E.≈-Reasoning


    transposeBifunctor₁-resp : ∀ {F G}
      → F ≈ G
      → transposeBifunctor₁ F ≈ transposeBifunctor₁ G
    transposeBifunctor₁-resp {F} {G} F≈G = record
        { iso = Fun.≈→≅ (Bifunctor→Functor₁-resp F≈G C.≅.refl)
        ; fmap-≈ = λ f x → sym (
            begin
              (back (iso F≈G) E.∘ fmap G (C.id , D.id) E.∘ E.id) E.∘
              fmap G (f , D.id) E.∘
              (E.id E.∘ fmap G (C.id , D.id)) E.∘ forth (iso F≈G)
            ≈⟨ assoc! E ⟩
              back (iso F≈G) E.∘
              (fmap G (C.id , D.id) E.∘ E.id E.∘ fmap G (f , D.id) E.∘ E.id E.∘ fmap G (C.id , D.id)) E.∘
              forth (iso F≈G)
            ≈⟨ E.∘-resp-r (E.∘-resp-l
                 (trans
                   (E.∘-resp-l (fmap-id G))
                   (E.∘-resp-r (E.∘-resp-r (E.∘-resp-r (E.∘-resp-r (fmap-id G))))))) ⟩
              back (iso F≈G) E.∘
              (E.id E.∘ E.id E.∘ fmap G (f , D.id) E.∘ E.id E.∘ E.id) E.∘
              forth (iso F≈G)
            ≈⟨ E.∘-resp-r (E.∘-resp-l (trans E.id-l (trans E.id-l
                 (trans (E.∘-resp-r E.id-l) E.id-r)))) ⟩
              back (iso F≈G) E.∘ fmap G (f , D.id) E.∘ forth (iso F≈G)
            ≈⟨ E.≈.sym (fmap-≈ F≈G _) ⟩
              fmap F (f , D.id)
            ∎
          )
        }
      where
        open E.≈-Reasoning
        open E.≈ using (sym ; trans)
        open _≈_ using (iso ; fmap-≈)


    Bifunctor→Functor₂ : Bifunctor C D E → D.Obj → Functor C E
    Bifunctor→Functor₂ F x = record
        { fobj = λ c → fobj F (c , x)
        ; fmap = λ f → fmap F (f , D.id)
        ; fmap-resp = λ x≈y → fmap-resp F (x≈y , D.≈.refl)
        ; fmap-id = fmap-id F
        ; fmap-∘ = λ where
            {f = f} {g} →
              begin
                fmap F (f , D.id) E.∘ fmap F (g , D.id)
              ≈⟨ fmap-∘ F ⟩
                fmap F (f C.∘ g , D.id D.∘ D.id)
              ≈⟨ fmap-resp F (C.≈.refl , D.id-l) ⟩
                fmap F (f C.∘ g , D.id)
              ∎
        }
      where
        open E.≈-Reasoning


    transposeBifunctor₂ : Bifunctor C D E → Functor D (Fun C E)
    transposeBifunctor₂ F = record
        { fobj = Bifunctor→Functor₂ F
        ; fmap = λ {a} {b} f → record
            { component = λ _ → fmap F (C.id , f)
            ; natural = λ {a′} {b′} {g} →
                begin
                  fmap F (C.id , f) E.∘ fmap (Bifunctor→Functor₂ F a) g
                ≈⟨ fmap-∘ F ⟩
                  fmap F (C.id C.∘ g , f D.∘ D.id)
                ≈⟨ fmap-resp F
                     ( (C.≈.trans C.id-l (C.≈.sym C.id-r))
                     , (D.≈.trans D.id-r (D.≈.sym D.id-l)) ) ⟩
                  fmap F (g C.∘ C.id , D.id D.∘ f)
                ≈⟨ E.≈.sym (fmap-∘ F) ⟩
                  fmap (Bifunctor→Functor₂ F b) g E.∘ fmap F (C.id , f)
                ∎
            }
        ; fmap-resp = λ x≈y _ → fmap-resp F (C.≈.refl , x≈y)
        ; fmap-id = λ _ → fmap-id F
        ; fmap-∘ = λ where
            {f = f} {g} _ →
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
