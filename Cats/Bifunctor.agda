module Cats.Bifunctor where

open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)

open import Cats.Category
open import Cats.Category.Cat.Facts.Product using (hasBinaryProducts)
open import Cats.Category.Fun using (Fun ; Trans)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Functor using (Functor)

open Functor
open Trans


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
      open E.≈-Reasoning
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
        ; fmap-∘ = λ f g →
            begin
              fmap F (C.id , f D.∘ g)
            ≈⟨ fmap-resp F (C.≈.sym C.id-l , D.≈.refl) ⟩
              fmap F (C.id C.∘ C.id , f D.∘ g)
            ≈⟨ fmap-∘ F _ _ ⟩
              fmap F (C.id , f) E.∘ fmap F (C.id , g)
            ∎
        }


    transposeBifunctor₁ : Bifunctor C D E
      → Functor C (Fun D E)
    transposeBifunctor₁ F = record
        { fobj = Bifunctor→Functor₁ F
        ; fmap = λ {a} {b} f → record
            { component = λ d → fmap F (f , D.id)
            ; natural = λ {a′} {b′} {g} →
                begin
                  fmap F (f , D.id) E.∘ fmap (Bifunctor→Functor₁ F a) g
                ≈⟨ E.≈.sym (fmap-∘ F _ _) ⟩
                  fmap F (f C.∘ C.id , D.id D.∘ g)
                ≈⟨ fmap-resp F
                    ( (C.≈.trans C.id-r (C.≈.sym C.id-l))
                    , D.≈.trans D.id-l (D.≈.sym D.id-r) ) ⟩
                  fmap F (C.id C.∘ f , g D.∘ D.id)
                ≈⟨ fmap-∘ F _ _ ⟩
                  fmap (Bifunctor→Functor₁ F b) g E.∘ fmap F (f , D.id)
                ∎
            }
        ; fmap-resp = λ x≈y d → fmap-resp F (x≈y , D.≈.refl)
        ; fmap-id = λ _ → fmap-id F
        ; fmap-∘ = λ f g d →
            begin
              fmap F (f C.∘ g , D.id)
            ≈⟨ fmap-resp F (C.≈.refl , D.≈.sym D.id-l) ⟩
              fmap F (f C.∘ g , D.id D.∘ D.id)
            ≈⟨ fmap-∘ F _ _ ⟩
              fmap F (f , D.id) E.∘ fmap F (g , D.id)
            ∎
        }


    Bifunctor→Functor₂ : Bifunctor C D E → D.Obj → Functor C E
    Bifunctor→Functor₂ F x = record
        { fobj = λ c → fobj F (c , x)
        ; fmap = λ f → fmap F (f , D.id)
        ; fmap-resp = λ x≈y → fmap-resp F (x≈y , D.≈.refl)
        ; fmap-id = fmap-id F
        ; fmap-∘ = λ f g →
            begin
              fmap F (f C.∘ g , D.id)
            ≈⟨ fmap-resp F (C.≈.refl , D.≈.sym D.id-l) ⟩
              fmap F (f C.∘ g , D.id D.∘ D.id)
            ≈⟨ fmap-∘ F _ _ ⟩
              fmap F (f , D.id) E.∘ fmap F (g , D.id)
            ∎
        }


    transposeBifunctor₂ : Bifunctor C D E
      → Functor D (Fun C E)
    transposeBifunctor₂ F = record
        { fobj = Bifunctor→Functor₂ F
        ; fmap = λ {a} {b} f → record
            { component = λ _ → fmap F (C.id , f)
            ; natural = λ {a′} {b′} {g} →
                begin
                  fmap F (C.id , f) E.∘ fmap (Bifunctor→Functor₂ F a) g
                ≈⟨ E.≈.sym (fmap-∘ F _ _) ⟩
                  fmap F (C.id C.∘ g , f D.∘ D.id)
                ≈⟨ fmap-resp F
                     ( (C.≈.trans C.id-l (C.≈.sym C.id-r))
                     , (D.≈.trans D.id-r (D.≈.sym D.id-l)) ) ⟩
                  fmap F (g C.∘ C.id , D.id D.∘ f)
                ≈⟨ fmap-∘ F _ _ ⟩
                  fmap (Bifunctor→Functor₂ F b) g E.∘ fmap F (C.id , f)
                ∎
            }
        ; fmap-resp = λ x≈y _ → fmap-resp F (C.≈.refl , x≈y)
        ; fmap-id = λ _ → fmap-id F
        ; fmap-∘ = λ f g _ →
            begin
              fmap F (C.id , f D.∘ g)
            ≈⟨ fmap-resp F (C.≈.sym C.id-l , D.≈.refl) ⟩
              fmap F (C.id C.∘ C.id , f D.∘ g)
            ≈⟨ fmap-∘ F _ _ ⟩
              fmap F (C.id , f) E.∘ fmap F (C.id , g)
            ∎
        }