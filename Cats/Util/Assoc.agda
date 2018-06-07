module Cats.Util.Assoc where

open import Level using (_⊔_ ; Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import Category.Monad using (RawMonad)
open import Data.Bool using (Bool ; true ; false ; not)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.String using (String)
open import Function using () renaming (_∘_ to _⊚_)
open import Reflection

open import Cats.Category.Base using (Category)

open RawMonad {{...}}

instance
  maybeMonad = Maybe.monad

  tcMonad : RawMonad {lzero} TC
  tcMonad = record
    { return = returnTC
    ; _>>=_ = bindTC
    }

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
  reassoc-canon ([ x ] ∷ r) = ∘-resp-r (reassoc-canon r)
  reassoc-canon ((ll ∷ lr) ∷ r) = ≈.trans assoc (reassoc-canon (ll ∷ lr ∷ r))


  reassoc : ∀ {A B} (t s : CompTree _⇒_ A B)
    → rightAssoc t ≡ rightAssoc s
    → render t ≈ render s
  reassoc t s eq
      = ≈.trans (reassoc-canon t)
          (≈.trans (≈.reflexive (≡.cong render eq)) (≈.sym (reassoc-canon s)))


------------------------------------------------------------------------------
-- Reflective magic
-------------------------------------------------------------------------------


boolPredToDecidable : ∀ {a} {A : Set a} → (f : A → Bool) → ∀ x → Dec (f x ≡ true)
boolPredToDecidable f x with f x
... | true = yes refl
... | false = no λ()


removeHiddenArguments : Term → Term
removeHiddenArguments (def n args)
    = def n (List.filter (boolPredToDecidable (not ⊚ isHidden)) args)
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


void : ∀ {f} {M : Set f → Set f} {{_ : RawMonad M}} → ∀ {A} → M A → M (Lift ⊤)
void m = m >>= λ _ → return (lift tt)


mapM : ∀ {a f} {M : Set f → Set f} {{_ : RawMonad M}}
  → ∀ {A : Set a} {B} → (A → M B) → List A → M (List B)
mapM f = sequence ⊚ List.map f


mapM′ : ∀ {a f} {M : Set f → Set f} {{_ : RawMonad M}}
  → ∀ {A : Set a} {B} → (A → M B) → List A → M (Lift ⊤)
mapM′ f = void ⊚ mapM f


fromArg : ∀ {A} → Arg A → A
fromArg (arg _ x) = x


fromAbs : ∀ {A} → Abs A → A
fromAbs (abs _ x) = x


-- This may or may not loop if there are metas in the input term that cannot be
-- solved when this tactic is called.
{-# TERMINATING #-}
blockOnAnyMeta : Term → TC (Lift ⊤)
blockOnAnyMeta (var x args) = mapM′ (blockOnAnyMeta ⊚ fromArg) args
blockOnAnyMeta (con c args) = mapM′ (blockOnAnyMeta ⊚ fromArg) args
blockOnAnyMeta (def f args) = mapM′ (blockOnAnyMeta ⊚ fromArg) args
blockOnAnyMeta (lam v t) = blockOnAnyMeta (fromAbs t)
blockOnAnyMeta (pat-lam cs args) = return _ -- TODO
blockOnAnyMeta (pi a b) =
    blockOnAnyMeta (fromArg a) >>= λ _ →
    blockOnAnyMeta (fromAbs b)
blockOnAnyMeta (sort s) = return _
blockOnAnyMeta (lit l) = return _
blockOnAnyMeta (meta x x₁) = blockOnMeta x
blockOnAnyMeta unknown = return _


macro
  assoc! : ∀ {lo la l≈} → Category lo la l≈ → Term → TC ⊤
  assoc! C hole
      = bindTC (inferType hole) λ goal →
        bindTC (blockOnAnyMeta goal) λ _ →
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
