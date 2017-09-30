module Cats.Util.ExtensionalEquality.Propositional where

open import Level
open import Relation.Binary using (Rel ; IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Cats.Util.ExtensionalEquality as Generic using (_≈[_]_)


module _ {a b} {A : Set a} {B : Set b} where

  infixr 4 _≈_


  _≈_ : Rel (A → B) (a ⊔ b)
  _≈_ = _≈[ _≡_ ]_


  isEquivalence : IsEquivalence _≈_
  isEquivalence = Generic.isEquivalence ≡.isEquivalence
