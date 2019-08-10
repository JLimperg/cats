module Cats.Axioms where

open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  funext : ∀ {a b} → Extensionality a b
