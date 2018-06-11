module Cats.Functor.Yoneda where

open import Data.Product using (_,_)
open import Relation.Binary using (Rel ; Setoid ; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Cats.Bifunctor using (transposeBifunctor₂)
open import Cats.Category
open import Cats.Category.Cat.Facts.Exponential using (Eval)
open import Cats.Category.Cat.Facts.Product using (First ; Swap)
open import Cats.Category.Fun using (Fun ; Trans)
open import Cats.Category.Fun.Facts using (NatIso→≅)
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Category.Setoids using (Setoids)
open import Cats.Functor using (Functor ; _∘_)
open import Cats.Functor.Op using (Op)
open import Cats.Functor.Representable using (Hom[_])
open import Cats.Util.SetoidReasoning

import Cats.Category.Constructions.Iso

open Functor
open Trans
open Cats.Category.Setoids.Build._⇒_
open Setoid using (Carrier ; isEquivalence)
module Iso = Cats.Category.Constructions.Iso.Build._≅_


-- We force C to be at l/l/l. Can we generalise to lo/la/l≈?
module _ {l} {C : Category l l l} where

  private
    Sets : Category _ _ _
    Sets = Setoids l l

    Presheaves : Category _ _ _
    Presheaves = Fun (C ᵒᵖ) Sets

    Funs : Category _ _ _
    Funs = Fun ((C ᵒᵖ) × Presheaves) Sets

    module C = Category C
    module Sets = Category Sets
    module Pre = Category Presheaves
    module Funs = Category Funs


  y : Functor C Presheaves
  y = transposeBifunctor₂ Hom[ C ]


  module _ (c : C.Obj) (F : Functor (C ᵒᵖ) (Sets)) where

    private
      module ycc≈ = IsEquivalence (isEquivalence (fobj (fobj y c) c))
      module Fc≈ = IsEquivalence (isEquivalence (fobj F c))


    forth : Pre.Hom (fobj y c) F Sets.⇒ fobj F c
    forth = record
        { arr = λ f → arr (component f c) C.id
        ; resp = λ f≈g → f≈g c ycc≈.refl
        }


    back-θ-component : Carrier (fobj F c) → (c′ : C.Obj) → C.Hom c′ c Sets.⇒ fobj F c′
    back-θ-component a c′ = record
        { arr = λ h → arr (fmap F h) a
        ; resp = λ f≈g → fmap-resp F f≈g Fc≈.refl
        }


    back-θ : Carrier (fobj F c) → fobj y c Pre.⇒ F
    back-θ a = record
        { component = back-θ-component a
        ; natural = λ {c′} {d′} {f} {g} {g′} g≈g′ →
            begin⟨ fobj F d′ ⟩
              arr (back-θ-component a d′ Sets.∘ fmap (fobj y c) f) g
            ≡⟨⟩
              arr (fmap F (C.id C.∘ g C.∘ f)) a
            ≈⟨ fmap-resp F (C.≈.trans C.id-l (C.∘-resp-l g≈g′)) Fc≈.refl ⟩
              arr (fmap F (g′ C.∘ f)) a
            ≈⟨ fmap-∘ F f g′ Fc≈.refl ⟩
              arr (fmap F f Sets.∘ fmap F g′) a
            ≡⟨⟩
              arr (fmap F f Sets.∘ back-θ-component a c′) g′
            ∎
        }


    back : fobj F c Sets.⇒ Pre.Hom (fobj y c) F
    back = record
        { arr = back-θ
        ; resp = λ f≈g c′ x≈y → fmap-resp F x≈y f≈g
        }


    back-forth : back Sets.∘ forth Sets.≈ Sets.id
    back-forth {θ} {θ′} θ≈θ′ c′ {f} {g} f≈g =
        begin⟨ fobj F c′ ⟩
          arr (component (arr (back Sets.∘ forth) θ) c′) f
        ≡⟨⟩
          arr (fmap F f Sets.∘ component θ c) C.id
        ≈⟨ Sets.≈.sym {A = C.Hom c c} {fobj F c′}
            {component θ c′ Sets.∘ fmap (fobj y c) f}
            {fmap F f Sets.∘ component θ c}
            (natural θ) C.≈.refl ⟩
          arr (component θ c′ Sets.∘ fmap (fobj y c) f) C.id
        ≡⟨⟩
          arr (component θ c′) (C.id C.∘ C.id C.∘ f)
        ≈⟨ resp (component θ c′) (C.≈.trans C.id-l C.id-l) ⟩
          arr (component θ c′) f
        ≈⟨ θ≈θ′ c′ f≈g ⟩
          arr (component θ′ c′) g
        ∎


    forth-back : forth Sets.∘ back Sets.≈ Sets.id
    forth-back {x} {y} x≈y = fmap-id F x≈y


    iso : fobj Hom[ Presheaves ] (fobj y c , F) Sets.≅ fobj F c
    iso = record
        { forth = forth
        ; back = back
        ; back-forth = λ {θ} {θ′} θ≈θ′ → back-forth {θ} {θ′} θ≈θ′
        ; forth-back = forth-back
        }


  yoneda : (Hom[ Presheaves ] ∘ First (Op y)) Funs.≅ (Eval ∘ Swap)
  yoneda = NatIso→≅ record
      { iso = λ { (c , F) → iso c F }
      ; forth-natural = λ where
          {c , F} {c′ , F′} {f , θ} {ι} {τ} ι≈τ →
            let module S = Setoid (fobj F′ c′) in
            triangle (fobj F′ c′) (arr (component (θ Pre.∘ ι) c′) f)
              ( begin⟨ fobj F′ c′ ⟩
                  arr (forth c′ F′ Sets.∘ fmap Hom[ Presheaves ]
                         (fmap (First {D = Presheaves ᵒᵖ} (Op y)) (f , θ)))
                      ι
                ≡⟨⟩
                  arr (forth c′ F′ Sets.∘
                         fmap Hom[ Presheaves ] (fmap (Op y) f , Pre.id Pre.∘ θ))
                      ι
                ≡⟨⟩
                  arr (forth c′ F′)
                      (arr (fmap Hom[ Presheaves ] (fmap y f , Pre.id Pre.∘ θ)) ι)
                ≡⟨⟩
                  arr (forth c′ F′) (Pre.id Pre.∘ θ Pre.∘ ι Pre.∘ fmap y f)
                ≡⟨⟩
                  arr (component (Pre.id Pre.∘ θ Pre.∘ ι Pre.∘ fmap y f) c′) C.id
                ≡⟨⟩
                  arr (component (Pre.id Pre.∘ θ Pre.∘ ι) c′ Sets.∘
                         component (fmap y f) c′)
                      C.id
                ≡⟨⟩
                  arr (component (Pre.id Pre.∘ θ Pre.∘ ι) c′) (f C.∘ C.id C.∘ C.id)
                ≈⟨ Pre.id-l {f = θ Pre.∘ ι} c′ (C.≈.trans (C.∘-resp-r C.id-r) C.id-r) ⟩
                  arr (component (θ Pre.∘ ι) c′) f
                ∎
              )

              ( begin⟨ fobj F′ c′ ⟩
                  arr (fmap F′ f Sets.∘ component θ c Sets.∘ forth c F) τ
                ≡⟨⟩
                  arr (fmap F′ f Sets.∘ component (θ Pre.∘ τ) c) C.id
                ≈⟨ S.sym (natural (θ Pre.∘ τ) (Setoid.refl (C.Hom c c))) ⟩
                  arr (component (θ Pre.∘ τ) c′ Sets.∘ fmap (fobj y c) f) C.id
                ≡⟨⟩
                  arr (component (θ Pre.∘ τ) c′) (C.id C.∘ C.id C.∘ f)
                ≈⟨ Pre.∘-resp-r {f = θ} {τ} {ι}
                     (Pre.≈.sym {i = ι} {τ} ι≈τ) c′ (C.≈.trans C.id-l C.id-l) ⟩
                  arr (component (θ Pre.∘ ι) c′) f
                ∎
              )
      }
