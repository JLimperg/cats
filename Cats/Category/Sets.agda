module Cats.Category.Sets where

open import Data.Product using (Σ ; _×_ ; proj₁ ; proj₂)
open import Level
open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Category
open import Cats.Util.ExtensionalEquality.Propositional
  using (_≈_ ; isEquivalence)
open import Cats.Util.Function
open import Cats.Util.Logic.Constructive


instance Sets : ∀ l → Category (suc l) l l
Sets l = record
    { Obj = Set l
    ; _⇒_ = λ A B → A → B
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = _∘_
    ; equiv = isEquivalence
    ; ∘-resp = ∘-resp
    ; id-r = ∘-id-r
    ; id-l = ∘-id-l
    ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → ∘-assoc {f = f} {g} {h}
    }


module _ {l} where

  open Category (Sets l) hiding (_≈_ ; id ; _∘_)


  Injective : ∀ {A B : Set l} → (A → B) → Set l
  Injective f = ∀ {a b} → f a ≡ f b → a ≡ b


  Injective→Mono : ∀ {A B : Set l} {f : A → B} → Injective f → IsMono f
  Injective→Mono inj f∘g≈f∘h x = inj (f∘g≈f∘h x)


  Mono→Injective :  ∀ {A B : Set l} {f : A → B} → IsMono f → Injective f
  Mono→Injective {f = f} mono {a} {b} fa≡fb = mono (λ _ → fa≡fb) (f b)


  Surjective : ∀ {A B : Set l} → (A → B) → Set l
  Surjective f = ∀ b → ∃[ a ] (f a ≡ b)


  Surjective→Epi : ∀ {A B : Set l} {f : A → B} → Surjective f → IsEpi f
  Surjective→Epi surj {g = g} {h} g∘f≈h∘f b with surj b
  ... | a , fa≡b
      = ≡.trans (≡.cong g (≡.sym fa≡b)) (≡.trans (g∘f≈h∘f a) (≡.cong h fa≡b))


  -- The proof that all epis are surjective is nonconstructive, so we omit it.


  exponentialIsProduct : ∀ {I A : Obj} → IsProduct {I = I} (λ _ → A) (I → A) (λ i f → f i)
  exponentialIsProduct projX
      = ∃!-intro
          (λ x i → projX i x)
          (λ _ _ → ≡.refl)
          (λ eq x → funext λ i → eq i x)
    where
      postulate
        funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (a : A) → B a}
          → (∀ x → f x ≡ g x)
          → f ≡ g


  Equ : ∀ {A B} (f g : A ⇒ B) → Set l
  Equ f g = ∃[ x ] (f x ≡ g x)


  -- TODO Move to a better location.
  cast : ∀ {a} {A B : Set a} → A ≡ B → A → B
  cast ≡.refl x = x


  -- TODO Move to a better location; rename.
  prod-eq-proj : ∀ {a b} {A : Set a} {B : A → Set b} {p q : Σ A B}
    → (eq₁ : proj₁ p ≡ proj₁ q)
    → cast (≡.cong B eq₁) (proj₂ p) ≡ proj₂ q
    → p ≡ q
  prod-eq-proj {p = p} {q} eq₁ eq₂ with p | q
  ... | p₁ , p₂ | q₁ , q₂ rewrite eq₁ | eq₂ = ≡.refl


  equalizer : ∀ {A B} (f g : A ⇒ B) → Equalizer f g
  equalizer {A} {B} f g = record
      { E = Equ f g
      ; e = proj₁
      ; isEqualizer = record
          { equalizes = λ x → proj₂ x
          ; universal = universal
          }
      }
    where
      universal : ∀ {Z} (z : Z ⇒ A) → f ∘ z ≈ g ∘ z → ∃![ u ] (proj₁ ∘ u ≈ z)
      universal {Z} z f∘z≈g∘z
          = ∃!-intro arr (λ _ → ≡.refl) unique
        where
          arr : Z ⇒ Equ f g
          arr x = z x , f∘z≈g∘z x

          unique : ∀ {h : Z ⇒ Equ f g} → proj₁ ∘ h ≈ z → arr ≈ h
          unique eq a = prod-eq-proj (≡.sym (eq a)) (≡.proof-irrelevance _ _)


module _ where

  -- TODO generalise to universe-polymorphic ⊤ and ⊥
  open Category (Sets zero)


  ⊥-Initial : IsInitial ⊥
  ⊥-Initial X = ∃!-intro (λ()) _ (λ _ ())


  ⊤-Terminal : IsTerminal ⊤
  ⊤-Terminal X = ∃!-intro (λ _ → ⊤-intro) _ (λ _ _ → ≡.refl)
