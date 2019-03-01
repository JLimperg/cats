module Cats.Category.Fun.Facts.Terminal where

open import Cats.Category
open import Cats.Category.Constructions.Terminal using (HasTerminal)
open import Cats.Category.Fun as Fun using (Fun)
open import Cats.Functor using (Functor)
open import Cats.Functor.Const using (Const)

open Functor


module Build {lo la l≈ lo′ la′ l≈′}
  {C : Category lo la l≈} {D : Category lo′ la′ l≈′}
  (D⊤ : HasTerminal D)
  where

  private
    module D = Category D
    module D⊤ = HasTerminal D⊤
    open Category (Fun C D) hiding (HasTerminal)


  One : Obj
  One = Const C D⊤.One


  ⇒One : ∀ {X} → X ⇒ One
  ⇒One {X} = record
    { component = λ c → D⊤.⇒One
    ; natural = D.≈.sym (D.≈.trans D.id-l D⊤.⇒One-unique)
    }


  ⇒One-unique : ∀ {X} {f : X ⇒ One} → ⇒One ≈ f
  ⇒One-unique = Fun.≈-intro D⊤.⇒One-unique


  isTerminal : IsTerminal One
  isTerminal X = record
    { arr = ⇒One
    ; unique = λ _ → ⇒One-unique
    }


  hasTerminal : HasTerminal (Fun C D)
  hasTerminal = record
    { One = One
    ; isTerminal = isTerminal
    }


open Build {{...}} public
