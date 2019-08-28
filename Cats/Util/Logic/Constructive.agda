{-# OPTIONS --without-K --safe #-}
module Cats.Util.Logic.Constructive where

open import Data.Empty public
  using (⊥ ; ⊥-elim)
open import Data.Product public
  using (_,_ ; ∃-syntax ; Σ-syntax)
  renaming (_×_ to _∧_ ; proj₁ to ∧-eliml ; proj₂ to ∧-elimr)
open import Data.Sum public
  using ()
  renaming (_⊎_ to _∨_ ; inj₁ to ∨-introl ; inj₂ to ∨-intror)
open import Data.Unit public
  using (⊤)
  renaming (tt to ⊤-intro)
open import Relation.Nullary public
  using (¬_)


-- De Morgan's constructive rules
module _ {p q} {P : Set p} {Q : Set q} where

  ¬∨¬→¬∧ : ¬ P ∨ ¬ Q → ¬ (P ∧ Q)
  ¬∨¬→¬∧ (∨-introl ¬p) (p , _) = ¬p p
  ¬∨¬→¬∧ (∨-intror ¬q) (_ , q) = ¬q q


  ¬∨→¬∧¬ : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q
  ¬∨→¬∧¬ ¬p∨q = (λ p → ¬p∨q (∨-introl p)) , (λ q → ¬p∨q (∨-intror q))


  ¬∧¬→¬∨ : ¬ P ∧ ¬ Q → ¬ (P ∨ Q)
  ¬∧¬→¬∨ (¬p , _) (∨-introl p) = ¬p p
  ¬∧¬→¬∨ (_ , ¬q) (∨-intror q) = ¬q q


-- Quantifiers and negation
module _ {u p} {U : Set u} {P : U → Set p} where

  ¬∃→∀¬ : ¬ (∃[ u ] (P u)) → ∀ u → ¬ P u
  ¬∃→∀¬ ¬∃ u pu = ¬∃ (u , pu)


  ∀¬→¬∃ : (∀ u → ¬ (P u)) → ¬ (∃[ u ] (P u))
  ∀¬→¬∃ ∀¬ (u , pu) = ∀¬ u pu


  ∃¬→¬∀ : ∃[ u ] (¬ P u) → ¬ (∀ u → P u)
  ∃¬→¬∀ (u , ¬pu) ∀upu = ¬pu (∀upu u)
