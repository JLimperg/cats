module Cats.Category.Sets where

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
    ; assoc = ∘-assoc
    }


module _ {l} where

  open Category (Sets l)


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


module _ where

  -- TODO generalise to universe-polymorphic ⊤ and ⊥
  open Category (Sets zero)


  ⊥-Initial : IsInitial ⊥
  ⊥-Initial X = (λ()) , λ _ ()


  ⊤-Terminal : IsTerminal ⊤
  ⊤-Terminal X = (λ _ → ⊤-intro) , λ _ _ → ≡.refl
