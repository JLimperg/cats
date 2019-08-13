module Cats.Limit.Product where

open import Data.Bool using (Bool ; true ; false)
open import Data.Product using (_×_ ; _,_ ; ∃-syntax ; proj₁ ; proj₂)

open import Cats.Category
open import Cats.Category.Cones using (Cones ; Cone ; HasObj-Cone)
open import Cats.Category.Discrete as Discrete using (Discrete)
open import Cats.Functor using (Functor)
open import Cats.Limit
open import Cats.Util.Conv


module _ {lo la l≈ li}
  {Cat : Category lo la l≈}
  {I : Set li} {O : I → Category.Obj Cat}
  where

  open Category Cat
  open Product using (isProduct)
  open Cone using (arr)


  F : Functor (Discrete I) Cat
  F = Discrete.functor I O


  private
    module Cones = Category (Cones F)


  productData→cone : ∀ {P} → (∀ i → P ⇒ O i) → Cone F
  productData→cone {P} proj = record
      { Apex = P
      ; arr = proj
      ; commute = λ { Discrete.id → ≈.sym id-l }
      }


  cone→productData : Cone F → ∃[ P ] (∀ i → P ⇒ O i)
  cone→productData c = c ᴼ , arr c


  terminal : ∀ {P} {proj : ∀ i → P ⇒ O i}
    → IsProduct O P proj
    → Cones.IsTerminal (productData→cone proj)
  terminal {P} {proj} isProduct c = record
      { arr = record
          { arr = θ
          ; commute = λ j → ≈.sym (∃!′.prop prod j)
          }
      ; unique = λ where
          {record { arr = θ′ ; commute = commute′ }} _ →
            ∃!′.unique prod (λ i → ≈.sym (commute′ i))
      }
    where
      prod : ∃![ u ] (∀ i → arr c i ≈ proj i ∘ u)
      prod = isProduct (arr c)

      θ : c ᴼ ⇒ P
      θ = prod ⃗


  product : ∀ {c}
    → Cones.IsTerminal c
    → let (P , proj) = cone→productData c
      in IsProduct O P proj
  product {c} term {X} x = record
      { arr = f
      ; prop = prop
      ; unique = uniq
      }
    where
      open Cats.Category.Cones._⇒_ using (arr ; commute)

      P = proj₁ (cone→productData c)
      proj = proj₂ (cone→productData c)

      u : Cones.∃! (productData→cone x) c
      u = term (productData→cone x)

      f : X ⇒ P
      f = arr (u ⃗)

      prop : ∀ i → x i ≈ proj i ∘ f
      prop i = ≈.sym (commute (u ⃗) _)

      uniq : IsUniqueSuchThat (λ g → ∀ i → x i ≈ proj i ∘ g) f
      uniq {g} eq = Cones.∃!′.unique u {f′} _
        where
          f′ : productData→cone x Cones.⇒ c
          f′ = record
              { arr = g
              ; commute = λ i → ≈.sym (eq i)
              }


  product→limit : Product O → Limit F
  product→limit P = record
      { cone = productData→cone (Product.proj P)
      ; isLimit = terminal (isProduct P)
      }


  limit→product : Limit F → Product O
  limit→product L
      = let (P , proj) = cone→productData (L ᴼ) in
        record
          { prod = P
          ; proj = proj
          ; isProduct = product (Limit.isLimit L)
          }


  product-unique : (P Q : Product O) → P ᴼ ≅ Q ᴼ
  product-unique P Q = obj-unique (product→limit P) (product→limit Q)
