module Cats.Limit.Product where

open import Data.Bool using (Bool ; true ; false)
open import Data.Product using (_×_ ; _,_ ; ∃-syntax ; proj₁ ; proj₂)

open import Cats.Category
open import Cats.Category.Cones using (Cones ; Cone)
open import Cats.Category.Discrete Bool as Two using () renaming
  (Discrete to Two)
open import Cats.Functor
open import Cats.Limit
open import Cats.Util.Conv


module _ {lo la l≈} {Cat : Category lo la l≈} {A B : Category.Obj Cat} where

  open Category Cat
  open BinaryProduct using (projl ; projr ; isBinaryProduct)
  open Cone using (arr)


  F : Functor Two Cat
  F = record
       { fobj = λ { true → A ; false → B }
       ; fmap = λ { Two.id → id }
       ; fmap-resp = λ { {A} {B} {Two.id} {Two.id}  _ → ≈.refl }
       ; fmap-id = ≈.refl
       ; fmap-∘ = λ { Two.id Two.id → ≈.sym id-l }
       }


  private
    module Cones = Category (Cones F)


  productData→cone : ∀ {P} → (P ⇒ A) → (P ⇒ B) → Cone F
  productData→cone {P} pl pr = record
      { Apex = P
      ; arr = λ { true → pl ; false → pr }
      ; commute = λ { Two.id → ≈.sym id-l }
      }


  cone→productData : Cone F → ∃[ P ] ((P ⇒ A) × (P ⇒ B))
  cone→productData c = c ᴼ , arr c true , arr c false


  terminal : ∀ {P} {pl : P ⇒ A} {pr : P ⇒ B}
    → IsBinaryProduct P pl pr
    → Cones.IsTerminal (productData→cone pl pr)
  terminal {P} {pl} {pr} isBinaryProduct c = record
      { arr = record
          { θ = θ
          ; commute = commute
          }
      ; unique = λ where
          {record { θ = θ′ ; commute = commute′ }} _ →
            ∃!′.unique prod (≈.sym (commute′ _) , ≈.sym (commute′ _))
      }
    where
      prod : ∃![ u ] (arr c true ≈ pl ∘ u × arr c false ≈ pr ∘ u)
      prod = isBinaryProduct (arr c true) (arr c false)

      θ : c ᴼ ⇒ P
      θ = prod ⃗

      commute : ∀ j → arr (productData→cone pl pr) j ∘ θ ≈ arr c j
      commute true  = ≈.sym (proj₁ (∃!′.prop prod))
      commute false = ≈.sym (proj₂ (∃!′.prop prod))


  product : ∀ {c}
    → Cones.IsTerminal c
    → let (P , pl , pr) = cone→productData c
      in IsBinaryProduct P pl pr
  product {c} term {X} xl xr = record
      { arr = f
      ; prop = prop
      ; unique = uniq
      }
    where
      open Cats.Category.Cones._⇒_ using (θ ; commute)

      P = proj₁ (cone→productData c)
      pl = proj₁ (proj₂ (cone→productData c))
      pr = proj₂ (proj₂ (cone→productData c))

      u : Cones.∃! (productData→cone xl xr) c
      u = term (productData→cone xl xr)

      f : X ⇒ P
      f = θ (u ⃗)

      prop : xl ≈ pl ∘ f × xr ≈ pr ∘ f
      prop = ≈.sym (commute (u ⃗) _) , ≈.sym (commute (u ⃗) _)

      uniq : IsUniqueSuchThat (λ g → xl ≈ pl ∘ g × xr ≈ pr ∘ g) f
      uniq {g} (eq₁ , eq₂) = Cones.∃!′.unique u {f′} _
        where
          f′ : productData→cone xl xr Cones.⇒ c
          f′ = record
              { θ = g
              ; commute = λ { true → ≈.sym eq₁ ; false → ≈.sym eq₂ }
              }


  product→limit : BinaryProduct A B → Limit F
  product→limit P = record
      { cone = productData→cone (projl P) (projr P)
      ; isTerminal = terminal (isBinaryProduct P)
      }


  limit→product : Limit F → BinaryProduct A B
  limit→product L
      = let (P , pl , pr) = cone→productData (L ᴼ) in
        record
          { prod = P
          ; projl = pl
          ; projr = pr
          ; isBinaryProduct = product (Limit.isTerminal L)
          }


  product-unique : (P Q : BinaryProduct A B) → P ᴼ ≅ Q ᴼ
  product-unique P Q = obj-unique F (product→limit P) (product→limit Q)
