module Cats.Category.Cat.Facts.Exponential where

open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)

open import Cats.Bifunctor using
  (Bifunctor ; Bifunctor→Functor₁ ; transposeBifunctor₁ ; transposeBifunctor₁-resp)
open import Cats.Category
open import Cats.Category.Cat as Cat using
  (Cat ; Functor ; _∘_ ; _≈_) renaming
  (id to Id)
open import Cats.Category.Cat.Facts.Product using (hasBinaryProducts ; ⟨_×_⟩)
open import Cats.Category.Fun using (Fun ; Trans)
open import Cats.Category.Fun.Facts using (NatIso ; NatIso→≅)
open import Cats.Category.Product.Binary using (_×_)
open import Cats.Util.Assoc using (assoc!)
open import Cats.Util.Conv

import Cats.Category.Base as Base
import Cats.Category.Constructions.Unique as Unique
import Cats.Category.Constructions.Iso as Iso

open Functor
open Trans
open Iso.Build._≅_


infixr 1 _↝_


_↝_ : ∀ {lo la l≈ lo′ la′ l≈′}
  → Category lo la l≈
  → Category lo′ la′ l≈′
  → Category (lo ⊔ la ⊔ l≈ ⊔ lo′ ⊔ la′ ⊔ l≈′) (lo ⊔ la ⊔ la′ ⊔ l≈′) (lo ⊔ l≈′)
_↝_ = Fun


module _ {lo la l≈ lo′ la′ l≈′}
  {B : Category lo la l≈} {C : Category lo′ la′ l≈′}
  where

  private
    module B = Category B
    module C = Category C
    module B↝C = Category (Fun B C)


  Eval : Bifunctor (B ↝ C) B C
  Eval = record
      { fobj = λ where
          (F , x) → fobj F x
      ; fmap = λ where
          {F , a} {G , b} (θ , f) → fmap G f C.∘ component θ a
      ; fmap-resp = λ where
          {F , a} {G , b} {θ , f} {ι , g} (θ≈ι , f≈g) →
            C.∘-resp (fmap-resp G f≈g) (θ≈ι a)
      ; fmap-id = λ { {F , b} → C.≈.trans (C.∘-resp-l (fmap-id F)) C.id-l }
      ; fmap-∘ = λ where
          {F , a} {G , b} {H , c} (θ , f) (ι , g) →
            begin
              fmap H (f B.∘ g) C.∘ component (θ B↝C.∘ ι) a
            ≈⟨ C.∘-resp-l (fmap-∘ H _ _) ⟩
              (fmap H f C.∘ fmap H g) C.∘ (component θ a C.∘ component ι a)
            ≈⟨ assoc! C ⟩
              fmap H f C.∘ (fmap H g C.∘ component θ a) C.∘ component ι a
            ≈⟨ C.∘-resp-r (C.∘-resp-l (C.≈.sym (natural θ))) ⟩
              fmap H f C.∘ (component θ b C.∘ fmap G g) C.∘ component ι a
            ≈⟨ assoc! C ⟩
              (fmap H f C.∘ component θ b) C.∘ (fmap G g C.∘ component ι a)
            ∎
      }
    where
      open C.≈-Reasoning


module _ {lo la l≈ lo′ la′ l≈′ lo″ la″ l≈″}
  {B : Category lo la l≈} {C : Category lo′ la′ l≈′} {D : Category lo″ la″ l≈″}
  where

  private
    module B = Category B
    module C = Category C
    module D = Category D
    module C↝D = Category (Fun C D)


  Curry : Bifunctor B C D → Functor B (C ↝ D)
  Curry F = transposeBifunctor₁ F


  Curry-resp : ∀ {F G} → F ≈ G → Curry F ≈ Curry G
  Curry-resp = transposeBifunctor₁-resp


  Curry-correct : ∀ {F} → Eval ∘ ⟨ Curry F × Id ⟩ ≈ F
  Curry-correct {F} = record
      { iso = D.≅.refl
      ; fmap-≈ = λ where
        {a , a′} {b , b′} (f , f′) →
          begin
            fmap (Eval ∘ ⟨ Curry F × Id ⟩) (f , f′)
          ≡⟨⟩
            fmap Eval (fmap (Curry F) f , f′)
          ≡⟨⟩
            fmap F (B.id , f′) D.∘ fmap F (f , C.id)
          ≈⟨ D.≈.sym (fmap-∘ F _ _) ⟩
            fmap F (B.id B.∘ f , f′ C.∘ C.id)
          ≈⟨ fmap-resp F (B.id-l , C.id-r) ⟩
            fmap F (f , f′)
          ≈⟨ D.≈.sym D.id-r ⟩
            fmap F (f , f′) D.∘ D.id
          ≈⟨ D.≈.sym D.id-l ⟩
            D.id D.∘ fmap F (f , f′) D.∘ D.id
          ∎
      }
    where
      open D.≈-Reasoning


  Curry-unique : ∀ {F Curry′}
    → Eval ∘ ⟨ Curry′ × Id ⟩ ≈ F
    → Curry′ ≈ Curry F
  Curry-unique {F} {Curry′} eq@record { iso = iso ; fmap-≈ = fmap-≈ } = record
      { iso = λ {x} →
          let open C↝D.≅-Reasoning in
          C↝D.≅.sym (
            begin
              fobj (Curry F) x
            ≈⟨ _≈_.iso (Curry-resp (sym-Cat eq)) ⟩
              fobj (Curry (Eval ∘ ⟨ Curry′ × Id ⟩)) x
            ≈⟨ NatIso→≅ (lem x) ⟩
              fobj Curry′ x
            ∎
          )
      ; fmap-≈ = λ {a} {b} f x → D.≈.sym (
          let open D.≈-Reasoning in
          begin
            ((D.id D.∘ D.id) D.∘
             (D.id D.∘ fmap (fobj Curry′ b) C.id D.∘ component (fmap Curry′ B.id) x) D.∘
             back iso
            ) D.∘
            fmap F (f , C.id) D.∘
            (forth iso D.∘ (fmap (fobj Curry′ a) C.id D.∘ component (fmap Curry′ B.id) x) D.∘ D.id) D.∘
            D.id D.∘ D.id
          ≈⟨ ∘-resp
               (trans (∘-resp-l id-l) (trans id-l (∘-resp-l (trans id-l
                 (∘-resp (fmap-id (fobj Curry′ b)) (fmap-id Curry′ x))))))
               (∘-resp-r (trans (∘-resp-r (id-r)) (trans id-r (∘-resp-r
                 (trans id-r (∘-resp (fmap-id (fobj Curry′ a)) (fmap-id Curry′ x))))))) ⟩
            ((D.id D.∘ D.id) D.∘ back iso) D.∘
            fmap F (f , C.id) D.∘
            (forth iso D.∘ (D.id D.∘ D.id))
          ≈⟨ ∘-resp
               (trans (∘-resp-l id-l) id-l)
               (∘-resp-r (trans (∘-resp-r id-l) id-r)) ⟩
            back iso D.∘ fmap F (f , C.id) D.∘ forth iso
          ≈⟨ sym (fmap-≈ (f , C.id)) ⟩
            fmap (fobj Curry′ b) C.id D.∘ component (fmap Curry′ f) x
          ≈⟨ trans (∘-resp-l (fmap-id (fobj Curry′ b))) id-l ⟩
            component (fmap Curry′ f) x
          ∎
        )
      }
    where
      open D using (id-l ; id-r ; ∘-resp ; ∘-resp-l ; ∘-resp-r)
      open D.≈ using (sym ; trans)
      open IsEquivalence Cat.equiv using () renaming (sym to sym-Cat)

      lem : ∀ x
        → NatIso (Bifunctor→Functor₁ (Eval ∘ ⟨ Curry′ × Id ⟩) x) (fobj Curry′ x)
      lem x = record
          { iso = λ y → D.≅.refl
          ; forth-natural = λ {a} {b} {f} →
              let open D.≈-Reasoning in
              begin
                D.id D.∘ fmap (fobj Curry′ x) f D.∘ component (fmap Curry′ B.id) a
              ≈⟨ D.id-l ⟩
                fmap (fobj Curry′ x) f D.∘ component (fmap Curry′ B.id) a
              ≈⟨ D.∘-resp-r (fmap-id Curry′ a) ⟩
                fmap (fobj Curry′ x) f D.∘ D.id
              ∎
          }


instance
  hasExponentials : ∀ l → HasExponentials (Cat l l l)
  hasExponentials l = record
      { _↝′_ = λ B C → record
          { Cᴮ = B ↝ C
          ; eval = Eval
          ; curry′ = λ F → record
              { arr = Curry F
              ; prop = Curry-correct {F = F}
              ; unique = λ {g} eq →
                  let open IsEquivalence Cat.equiv using (sym) in
                  sym (Curry-unique eq)
              }
          }
      }
