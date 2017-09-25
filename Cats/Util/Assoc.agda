module Cats.Util.Assoc where

open import Level using (_⊔_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Category.Monad using (RawMonad)
open import Data.Bool using (Bool ; true ; false ; not)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.String using (String)
open import Reflection

open import Cats.Category using (Category)

open RawMonad {{...}}

instance
  maybeMonad = Maybe.monad

  sumMonad : ∀ {a b} {A : Set a} → RawMonad {a ⊔ b} (A ⊎_)
  sumMonad = record
      { return = inj₂
      ; _>>=_ = λ where
          (inj₁ a) _ → inj₁ a
          (inj₂ b) f → f b
      }


infixr 5 _∷_


Error : ∀ {a} (A : Set a) → Set a
Error A = String ⊎ A


error : ∀ {a} {A : Set a} → String → Error A
error = inj₁


argD : Term → Arg Term
argD = arg (arg-info visible relevant)




data CompTree {o a} {O : Set o} (A : O → O → Set a) : O → O → Set (o ⊔ a) where
  [_] : ∀ {x y} → A x y → CompTree A x y
  _∷_ : ∀ {x y z} (l : CompTree A y z) (r : CompTree A x y) → CompTree A x z


-- TODO We can translate this to well-founded recursion, using the height of the
-- left subtree as a termination measure.
{-# TERMINATING #-}
rightAssoc : ∀ {o a} {O : Set o} {A : O → O → Set a} {x y}
  → CompTree A x y
  → CompTree A x y
rightAssoc [ x ] = [ x ]
rightAssoc ([ x ] ∷ r) = [ x ] ∷ rightAssoc r
rightAssoc ((ll ∷ lr) ∷ r) = rightAssoc (ll ∷ (lr ∷ r))


module _ {lo la l≈} (C : Category lo la l≈) where

  open Category C

  render : ∀ {A B} → CompTree _⇒_ A B → A ⇒ B
  render [ x ] = x
  render (l ∷ r) = render l ∘ render r


  {-# TERMINATING #-}
  reassoc-canon : ∀ {A B} (t : CompTree _⇒_ A B)
    → render t ≈ render (rightAssoc t)
  reassoc-canon [ x ] = ≈.refl
  reassoc-canon ([ x ] ∷ r) = ∘-resp ≈.refl (reassoc-canon r)
  reassoc-canon ((ll ∷ lr) ∷ r) = ≈.trans (assoc _ _ _) (reassoc-canon (ll ∷ lr ∷ r))


  reassoc : ∀ {A B} (t s : CompTree _⇒_ A B)
    → rightAssoc t ≡ rightAssoc s
    → render t ≈ render s
  reassoc t s eq
      = ≈.trans (reassoc-canon t)
          (≈.trans (≈.reflexive (≡.cong render eq)) (≈.sym (reassoc-canon s)))


------------------------------------------------------------------------------
-- Reflective magic
------------------------------------------------------------------------------


removeHiddenArguments : Term → Term
removeHiddenArguments (def n args) = def n (List.filter (λ x → not (isHidden x)) args)
  where
    isHidden : ∀ {A} → Arg A → Bool
    isHidden (arg (arg-info hidden r) x) = true
    isHidden _ = false
removeHiddenArguments t = t


{-# TERMINATING #-}
collectTree : Term → Term
collectTree t with removeHiddenArguments t
... | def (quote Category._∘_) (arg _ _ ∷ arg _ l ∷ arg _ r ∷ [])
    = con (quote CompTree._∷_) (argD (collectTree l) ∷ argD (collectTree r) ∷ [])
... | _ = con (quote CompTree.[_]) (argD t ∷ [])


matchGoal : Type → Error (Term × Term)
matchGoal t with removeHiddenArguments t
... | def (quote Category._≈_) (arg _ _ ∷ arg _ lhs ∷ arg _ rhs ∷ [])
    = return (collectTree lhs , collectTree rhs)
... | _ = error "match-goal: no equality at top level"


sequence : ∀ {f} {M : Set f → Set f} {A} {{_ : RawMonad M}} → List (M A) → M (List A)
sequence [] = return []
sequence (x ∷ xs)
    = x >>= λ x' →
      sequence xs >>= λ xs' →
      return (x' ∷ xs')

macro
  assoc! : ∀ {lo la l≈} → Category lo la l≈ → Term → TC ⊤
  assoc! C hole
      = bindTC (inferType hole) λ goal →
        bindTC (normalise goal) λ goalN →
        bindTC (embedError goal (matchGoal goalN)) λ lhsrhs →
        let (lhs , rhs) = lhsrhs in
        bindTC (quoteTC C) λ Cname →
        let solution
              = def (quote reassoc)
                  ( argD Cname
                  ∷ argD lhs
                  ∷ argD rhs
                  ∷ argD (con (quote ≡.refl) [])
                  ∷ [])
        in
        unify hole solution
    where
      embedError : ∀ {a} {A : Set a} → Term → Error A → TC A
      embedError goal (inj₁ err)
          = typeError
          ( strErr err
          ∷ strErr "while trying to construct a member of type"
          ∷ termErr goal
          ∷ [])
      embedError _ (inj₂ t) = returnTC t
