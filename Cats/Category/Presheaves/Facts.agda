module Cats.Category.Presheaves.Facts where

open import Cats.Category
open import Cats.Category.Presheaves

import Cats.Category.Fun.Facts as Fun
import Cats.Category.Setoids.Facts


module _ {lo la l≈} {C : Category lo la l≈} {l l′} where

  -- We don't just re-export the following definitions from Fun because
  -- we want to fill in their instance arguments.

  instance
    hasBinaryProducts : HasBinaryProducts (Presheaves C l l′)
    hasBinaryProducts = Fun.hasBinaryProducts


    hasTerminal : HasTerminal (Presheaves C l l′)
    hasTerminal = Fun.hasTerminal


    hasFiniteProducts : HasFiniteProducts (Presheaves C l l′)
    hasFiniteProducts = Fun.hasFiniteProducts
