module Cats.Category where

open import Data.Bool using (Bool ; true ; false ; not)
open import Level
open import Relation.Binary using
  (Rel ; IsEquivalence ; _Preserves₂_⟶_⟶_ ; Setoid)

open import Cats.Util.Logic.Constructive

import Relation.Binary.EqReasoning as EqReasoning

import Cats.Category.Base as Base
import Cats.Category.Constructions.Epi as Epi
import Cats.Category.Constructions.Equalizer as Equalizer
import Cats.Category.Constructions.Iso as Iso
import Cats.Category.Constructions.Initial as Initial
import Cats.Category.Constructions.Mono as Mono
import Cats.Category.Constructions.Product as Product
import Cats.Category.Constructions.Terminal as Terminal
import Cats.Category.Constructions.Unique as Unique


Category : ∀ lo la l≈ → Set (suc (lo ⊔ la ⊔ l≈))
Category = Base.Category


module Category {lo la l≈} (Cat : Base.Category lo la l≈) where

  open Base.Category Cat public
  open Epi.Build Cat public
  open Equalizer.Build Cat public
  open Initial.Build Cat public
  open Iso.Build Cat public
  open Mono.Build Cat public
  open Product.Build Cat public
  open Terminal.Build Cat public
  open Unique.Build Cat public


open Product public using (HasBinaryProducts)
