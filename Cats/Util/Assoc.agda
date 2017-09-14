module Cats.Util.Assoc where

open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Category using (Category)


infixr 5 _∷_


data Telescope {u a} {U : Set u} (A : U → U → Set a) : U → U → Set (u ⊔ a)
  where
  [_] : ∀ {x y} → A x y → Telescope A x y
  _∷_ : ∀ {x y z} → A y z → Telescope A x y → Telescope A x z


module _ {u a} {U : Set u} {A : U → U → Set a} where

  infixr 5 _++_


  map : ∀ {b} {B : U → U → Set b}
    → (∀ {x y} → A x y → B x y) → ∀ {x y} → Telescope A x y → Telescope B x y
  map F [ f ]    = [ F f ]
  map F (f ∷ fs) = F f ∷ map F fs


  fold : (∀ {x y z} → A x y → A y z → A x z) → ∀ {x y} → Telescope A x y → A x y
  fold _∘_ [ x ] = x
  fold _∘_ (x ∷ xs) = (fold _∘_ xs) ∘ x


  _++_ : ∀ {x y z} → Telescope A x y → Telescope A y z → Telescope A x z
  xs ++ [ x ] = x ∷ xs
  xs ++ (x ∷ ys) = x ∷ (xs ++ ys)


concat : ∀ {u a} {U : Set u} {A : U → U → Set a} {x y}
  → Telescope (Telescope A) x y → Telescope A x y
concat = fold _++_


module _ {lo la l≈} (C : Category lo la l≈) where

  open Category C


  ⊕ : ∀ {A B} → Telescope _⇒_ A B → A ⇒ B
  ⊕ [ x ] = x
  ⊕ (x ∷ xs) = x ∘ ⊕ xs


  ⊕-++ : ∀ {A B C} (xs : Telescope _⇒_ A B) (ys : Telescope _⇒_ B C)
    → (⊕ (xs ++ ys)) ≈ (⊕ ys ∘ ⊕ xs)
  ⊕-++ xs [ x ] = ≈.refl
  ⊕-++ xs (x ∷ ys)
      = ≈.trans (∘-preserves-≈ (≈.refl) (⊕-++ xs ys)) (≈.sym (∘-assoc _ _ _))


  reassoc-canon : ∀ {A B} (xs : Telescope (Telescope _⇒_) A B)
    → ⊕ (map ⊕ xs) ≈ ⊕ (concat xs)
  reassoc-canon [ xs ] = ≈.refl
  reassoc-canon (xs ∷ xss)
      = ≈.trans (∘-preserves-≈ ≈.refl (reassoc-canon xss)) (≈.sym (⊕-++  _ xs))


  reassoc : ∀ {A B} (xs ys : Telescope (Telescope _⇒_) A B)
    → concat xs ≡ concat ys
    → ⊕ (map ⊕ xs) ≈ ⊕ (map ⊕ ys)
  reassoc xs ys eq
      = ≈.trans (reassoc-canon xs)
          (≈.trans (≈.reflexive (≡.cong ⊕ eq)) (≈.sym (reassoc-canon ys)))
