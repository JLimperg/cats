module Cats.Util.Reflection where

open import Reflection as Base hiding (return ; _>>_ ; _>>=_) public

open import Data.List using ([])
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Level using (zero ; Lift)

open import Cats.Util.Monad using (RawMonad ; _>>=_ ; _>>_ ; return ; mapM′)


instance
  tcMonad : ∀ {l} → RawMonad {l} TC
  tcMonad = record
      { return = Base.return
      ; _>>=_ = Base._>>=_
      }


pattern argH x = arg (arg-info hidden relevant) x
pattern argD x = arg (arg-info visible relevant) x
pattern defD x = def x []


fromArg : ∀ {A} → Arg A → A
fromArg (arg _ x) = x


fromAbs : ∀ {A} → Abs A → A
fromAbs (abs _ x) = x


blockOnAnyMeta-clause : Clause → TC (Lift zero ⊤)

-- This may or may not loop if there are metas in the input term that cannot be
-- solved when this tactic is called.
{-# TERMINATING #-}
blockOnAnyMeta : Term → TC (Lift zero ⊤)
blockOnAnyMeta (var x args) = mapM′ (blockOnAnyMeta ∘ fromArg) args
blockOnAnyMeta (con c args) = mapM′ (blockOnAnyMeta ∘ fromArg) args
blockOnAnyMeta (def f args) = mapM′ (blockOnAnyMeta ∘ fromArg) args
blockOnAnyMeta (lam v t) = blockOnAnyMeta (fromAbs t)
blockOnAnyMeta (pat-lam cs args) = do
    mapM′ blockOnAnyMeta-clause cs
    mapM′ (blockOnAnyMeta ∘ fromArg) args
blockOnAnyMeta (pi a b) = do
    blockOnAnyMeta (fromArg a)
    blockOnAnyMeta (fromAbs b)
blockOnAnyMeta (sort (set t)) = blockOnAnyMeta t
blockOnAnyMeta (sort (lit n)) = return _
blockOnAnyMeta (sort unknown) = return _
blockOnAnyMeta (lit l) = return _
blockOnAnyMeta (meta x _) = blockOnMeta x
blockOnAnyMeta unknown = return _

blockOnAnyMeta-clause (clause ps t) = blockOnAnyMeta t
blockOnAnyMeta-clause (absurd-clause ps) = return _
