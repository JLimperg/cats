{-# OPTIONS --without-K #-}
module Cats.Util.Logic.Classical where

open import Cats.Util.Logic.Constructive public


-- (Strong) law of the excluded middle
postulate lem : ∀ {p} (P : Set p) → P ∨ ¬ P


-- Double negation elimination
¬¬-elim : ∀ {p} {P : Set p} → ¬ ¬ P → P
¬¬-elim {P = P} ¬¬p with lem P
... | ∨-introl  p = p
... | ∨-intror ¬p = ⊥-elim (¬¬p ¬p)


-- Contrapositive
contrapositive : ∀ {p q} {P : Set p} {Q : Set q}
  → (¬ Q → ¬ P) → P → Q
contrapositive {P = P} {Q} contra p with lem Q
... | ∨-introl q = q
... | ∨-intror ¬q = ⊥-elim (contra ¬q p)


-- De Morgan's nonconstructive rule
¬∧→¬∨¬ : ∀ {p q} {P : Set p} {Q : Set q}
  → ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
¬∧→¬∨¬ {P = P} {Q} ¬p∧q with lem P | lem Q
... | ∨-introl p  | ∨-introl q  = ⊥-elim (¬p∧q (p , q))
... | ∨-introl _  | ∨-intror ¬q = ∨-intror ¬q
... | ∨-intror ¬p | _           = ∨-introl ¬p


-- Negation and ∀
¬∀→∃¬ : ∀ {u p} {U : Set u} {P : U → Set p}
  → ¬ (∀ u → P u) → ∃[ u ] (¬ P u)
¬∀→∃¬ ¬∀ = ¬¬-elim (λ ¬∃¬ → ¬∀ (λ u → ¬¬-elim (λ pu → ¬∃¬ (u , pu))))
