module Cats.Category.Sets where

open import Level
open import Relation.Binary using (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Category
open import Cats.Util.Logic.Constructive


infixr 9 _∘_
infixr 4 _≈_


_∘_ : ∀ {l} {A B C : Set l} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

id : ∀ {l} {A : Set l} → A → A
id x = x

-- We could generalise this to an arbitrary underlying equivalence relation in
-- place of _≡_.
_≈_ : ∀ {la lb} {A : Set la} {B : Set lb} → Rel (A → B) (la ⊔ lb)
f ≈ g = ∀ x → f x ≡ g x

≈-equiv : ∀ {la lb} {A : Set la} {B : Set lb}
  → IsEquivalence (_≈_ {A = A} {B})
≈-equiv = record
    { refl = λ _ → ≡.refl
    ; sym = λ eq x → ≡.sym (eq x)
    ; trans = λ eq₁ eq₂ x → ≡.trans (eq₁ x) (eq₂ x)
    }

∘-preserves-≈ : ∀ {l} {A B C : Set l}
  → (_∘_ {A = A} {B} {C}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
∘-preserves-≈ {x = f} {g} {h} {i} f≈g h≈i x
    = ≡.trans (≡.cong f (h≈i x)) (f≈g (i x))

id-identity-r : ∀ {l} {A B : Set l} {f : A → B} → f ∘ id ≈ f
id-identity-r _ = ≡.refl

id-identity-l : ∀ {l} {A B : Set l} {f : A → B} → id ∘ f ≈ f
id-identity-l _ = ≡.refl

∘-assoc : ∀ {l} {A B C D : Set l} (f : C → D) (g : B → C) (h : A → B)
  → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
∘-assoc _ _ _ _ = ≡.refl


instance Sets : ∀ l → Category (suc l) l l
Sets l = record
    { Obj = Set l
    ; _⇒_ = λ A B → A → B
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = _∘_
    ; ≈-equiv = ≈-equiv
    ; ∘-preserves-≈ = ∘-preserves-≈
    ; id-identity-r = id-identity-r
    ; id-identity-l = id-identity-l
    ; ∘-assoc = ∘-assoc
    }


Injective : ∀ {l} {A B : Set l} → (A → B) → Set l
Injective f = ∀ {a b} → f a ≡ f b → a ≡ b


Injective→Mono : ∀ {l} {A B : Set l} {f : A → B} → Injective f → IsMono f
Injective→Mono inj f∘g≈f∘h x = inj (f∘g≈f∘h x)


Mono→Injective :  ∀ {l} {A B : Set l} {f : A → B} → IsMono f → Injective f
Mono→Injective {f = f} mono {a} {b} fa≡fb = mono (λ _ → fa≡fb) (f b)


Surjective : ∀ {l} {A B : Set l} → (A → B) → Set l
Surjective f = ∀ b → ∃[ a ] (f a ≡ b)


Surjective→Epi : ∀ {l} {A B : Set l} {f : A → B} → Surjective f → IsEpi f
Surjective→Epi surj {g = g} {h} g∘f≈h∘f b with surj b
... | a , fa≡b
    = ≡.trans (≡.cong g (≡.sym fa≡b)) (≡.trans (g∘f≈h∘f a) (≡.cong h fa≡b))


-- The proof that all epis are surjective is nonconstructive, so we omit it.


⊥-Initial : IsInitial ⊥
⊥-Initial X = (λ()) , λ _ x → ⊥-elim x


⊤-Terminal : IsTerminal ⊤
⊤-Terminal X = (λ _ → ⊤-intro) , λ _ _ → ≡.refl
