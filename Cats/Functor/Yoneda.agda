module Cats.Functor.Yoneda where

open import Data.Product using (_,_)
open import Relation.Binary using (Rel ; Setoid ; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Cats.Bifunctor using (transposeBifunctor₂)
open import Cats.Category
open import Cats.Category.Cat.Facts.Exponential using (Eval)
open import Cats.Category.Cat.Facts.Product using (First ; Swap)
open import Cats.Category.Fun using (_↝_ ; Trans ; ≈-intro ; ≈-elim)
open import Cats.Category.Fun.Facts using (NatIso→≅)
open import Cats.Category.Op using (_ᵒᵖ)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Category.Setoids using (Setoids ; ≈-intro ; ≈-elim ; ≈-elim′)
open import Cats.Functor using
  ( Functor ; _∘_ ; IsFull ; IsFaithful ; IsEmbedding ; Embedding→Full
  ; Embedding→Faithful )
open import Cats.Functor.Op using (Op)
open import Cats.Functor.Representable using (Hom[_])
open import Cats.Util.SetoidMorphism.Iso using (IsIso-resp)
open import Cats.Util.SetoidReasoning

import Cats.Category.Constructions.Iso

open Functor
open Trans
open Cats.Category.Setoids._⇒_
open Setoid using (Carrier)


-- We force C to be at l/l/l. Can we generalise to lo/la/l≈?
module _ {l} {C : Category l l l} where

  private
    Sets : Category _ _ _
    Sets = Setoids l l

    Presheaves : Category _ _ _
    Presheaves = C ᵒᵖ ↝ Sets

    Funs : Category _ _ _
    Funs = (C ᵒᵖ) × Presheaves ↝ Sets

    module C = Category C
    module Sets = Category Sets
    module Pre = Category Presheaves
    module Funs = Category Funs


  y : Functor C Presheaves
  y = transposeBifunctor₂ Hom[ C ]


  module _ (c : C.Obj) (F : Functor (C ᵒᵖ) (Sets)) where

    private
      module ycc≈ = Setoid (fobj (fobj y c) c)
      module Fc≈ = Setoid (fobj F c)


    forth : Pre.Hom (fobj y c) F Sets.⇒ fobj F c
    forth = record
        { arr = λ f → arr (component f c) C.id
        ; resp = λ f≈g → ≈-elim′ (≈-elim f≈g)
        }


    back-θ-component : Carrier (fobj F c) → (c′ : C.Obj) → C.Hom c′ c Sets.⇒ fobj F c′
    back-θ-component a c′ = record
        { arr = λ h → arr (fmap F h) a
        ; resp = λ f≈g → ≈-elim′ (fmap-resp F f≈g)
        }


    back-θ : Carrier (fobj F c) → fobj y c Pre.⇒ F
    back-θ a = record
        { component = back-θ-component a
        ; natural = λ {c′} {d′} {f} → ≈-intro λ {g} {g′} g≈g′ →
            begin⟨ fobj F d′ ⟩
              arr (back-θ-component a d′ Sets.∘ fmap (fobj y c) f) g
            ≡⟨⟩
              arr (fmap F (C.id C.∘ g C.∘ f)) a
            ≈⟨ ≈-elim′ (fmap-resp F (C.≈.trans C.id-l (C.∘-resp-l g≈g′))) ⟩
              arr (fmap F (g′ C.∘ f)) a
            ≈˘⟨ ≈-elim′ (fmap-∘ F) ⟩
              arr (fmap F f Sets.∘ fmap F g′) a
            ≡⟨⟩
              arr (fmap F f Sets.∘ back-θ-component a c′) g′
            ∎
        }


    back : fobj F c Sets.⇒ Pre.Hom (fobj y c) F
    back = record
        { arr = back-θ
        ; resp = λ f≈g → ≈-intro (≈-intro λ x≈y → ≈-elim (fmap-resp F x≈y) f≈g)
        }


    back-forth : back Sets.∘ forth Sets.≈ Sets.id
    back-forth = ≈-intro λ {θ} {θ′} θ≈θ′ → ≈-intro λ {c′} → ≈-intro λ {f} {g} f≈g →
        begin⟨ fobj F c′ ⟩
          arr (component (arr (back Sets.∘ forth) θ) c′) f
        ≡⟨⟩
          arr (fmap F f Sets.∘ component θ c) C.id
        ≈⟨ ≈-elim′ (Sets.≈.sym (natural θ)) ⟩
          arr (component θ c′ Sets.∘ fmap (fobj y c) f) C.id
        ≡⟨⟩
          arr (component θ c′) (C.id C.∘ C.id C.∘ f)
        ≈⟨ resp (component θ c′) (C.≈.trans C.id-l C.id-l) ⟩
          arr (component θ c′) f
        ≈⟨ ≈-elim (≈-elim θ≈θ′) f≈g ⟩
          arr (component θ′ c′) g
        ∎


    forth-back : forth Sets.∘ back Sets.≈ Sets.id
    forth-back = ≈-intro λ x≈y → ≈-elim (fmap-id F) x≈y


    iso : fobj Hom[ Presheaves ] (fobj y c , F) Sets.≅ fobj F c
    iso = record
        { forth = forth
        ; back = back
        ; back-forth = back-forth
        ; forth-back = forth-back
        }


  yoneda : (Hom[ Presheaves ] ∘ First (Op y)) Funs.≅ (Eval ∘ Swap)
  yoneda = NatIso→≅ record
      { iso = λ { {c , F} → iso c F }
      ; forth-natural = λ where
          {c , F} {c′ , F′} {f , θ} → ≈-intro λ {ι} {τ} ι≈τ →
            triangle (fobj F′ c′) (arr (component (θ Pre.∘ ι) c′) f)
              ( begin⟨ fobj F′ c′ ⟩
                  arr (forth c′ F′ Sets.∘ fmap Hom[ Presheaves ]
                         (fmap (First {D = Presheaves ᵒᵖ} (Op y)) (f , θ)))
                      ι
                ≡⟨⟩
                  arr (component (Pre.id Pre.∘ θ Pre.∘ ι) c′) (f C.∘ C.id C.∘ C.id)
                ≈⟨ ≈-elim (≈-elim (Pre.id-l {f = θ Pre.∘ ι}))
                    (C.≈.trans (C.∘-resp-r C.id-r) C.id-r) ⟩
                  arr (component (θ Pre.∘ ι) c′) f
                ∎
              )

              ( begin⟨ fobj F′ c′ ⟩
                  arr (fmap F′ f Sets.∘ component θ c Sets.∘ forth c F) τ
                ≡⟨⟩
                  arr (fmap F′ f Sets.∘ component (θ Pre.∘ τ) c) C.id
                ≈˘⟨ ≈-elim′ (natural (θ Pre.∘ τ)) ⟩
                  arr (component (θ Pre.∘ τ) c′ Sets.∘ fmap (fobj y c) f) C.id
                ≡⟨⟩
                  arr (component (θ Pre.∘ τ) c′) (C.id C.∘ C.id C.∘ f)
                ≈⟨ ≈-elim (≈-elim (Pre.∘-resp-r {f = θ} (Pre.≈.sym {i = ι} {τ} ι≈τ)))
                    (C.≈.trans C.id-l C.id-l) ⟩
                  arr (component (θ Pre.∘ ι) c′) f
                ∎
              )
      }


  back≈sfmap : ∀ {a b} → back a (fobj y b) Sets.≈ sfmap y
  back≈sfmap = ≈-intro λ {f} {g} f≈g → ≈-intro (≈-intro λ {x} {y} x≈y →
      begin⟨ C.Hom _ _ ⟩
        C.id C.∘ f C.∘ x
      ≈⟨ C.id-l ⟩
        f C.∘ x
      ≈⟨ C.∘-resp f≈g x≈y ⟩
        g C.∘ y
      ≈⟨ C.≈.sym C.id-r ⟩
        (g C.∘ y) C.∘ C.id
      ≈⟨ C.assoc ⟩
        g C.∘ y C.∘ C.id
      ∎)


  y-Embedding : IsEmbedding y
  y-Embedding {a} {b} = IsIso-resp back≈sfmap record
      { back = forth a (fobj y b)
      ; forth-back = back-forth a (fobj y b)
      ; back-forth = forth-back a (fobj y b)
      }


  y-Full : IsFull y
  y-Full = Embedding→Full y y-Embedding


  y-Faithful : IsFaithful y
  y-Faithful = Embedding→Faithful y y-Embedding
