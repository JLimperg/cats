module Cats.Util.Simp where

open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; ∃-syntax)
open import Data.Unit using (⊤)
open import Function using () renaming (_∘_ to _⊚_)
open import Level using (_⊔_) renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality as ≡ using
  (_≡_ ; inspect ; [_])

open import Cats.Category.Base
open import Cats.Util.Reflection

_>>=_ = bindTC
return = returnTC

_>>_ : ∀ {a} {A : Set a} {b} {B : Set b} → TC A → TC B → TC B
ma >> mb = ma >>= λ _ → mb


module _ {lo la l≈} (C : Category lo la l≈) where

  infixr 9 _∘_

  private
    module C = Category C
    module ≈ = C.≈
    open C.≈-Reasoning


  data Tm : C.Obj → C.Obj → Set (lo ⊔ la) where
    var : ∀ {A B} → A C.⇒ B → Tm A B
    id : ∀ {A} → Tm A A
    _∘_ : ∀ {A B C} → Tm B C → Tm A B → Tm A C


  ⟦_⟧ : ∀ {A B} → Tm A B → A C.⇒ B
  ⟦ var f ⟧ = f
  ⟦ id ⟧ = C.id
  ⟦ f ∘ g ⟧ = ⟦ f ⟧ C.∘ ⟦ g ⟧


  Method : Set (lo ⊔ la)
  Method = ∀ {A B} → Tm A B → Tm A B


  Correct : Method → Set (lo ⊔ la ⊔ l≈)
  Correct f = ∀ {A B} (t : Tm A B) → ⟦ t ⟧ C.≈ ⟦ f t ⟧


  Correct→Injective : (f : Method) → Correct f → ∀ {A B} (t u : Tm A B)
    → ⟦ f t ⟧ C.≈ ⟦ f u ⟧
    → ⟦ t ⟧ C.≈ ⟦ u ⟧
  Correct→Injective f fcor t u eq
      = ≈.trans (fcor t) (≈.trans eq (≈.sym (fcor u)))


  ⊚-correct : (f g : Method) → Correct f → Correct g → Correct (f ⊚ g)
  ⊚-correct _ _ fcor gcor t = ≈.trans (gcor _) (fcor _)


  {-# TERMINATING #-}
  reassoc : Method
  reassoc (var f) = var f
  reassoc id = id
  reassoc (var f ∘ g) = var f ∘ reassoc g
  reassoc (id ∘ g) = id ∘ reassoc g
  reassoc ((f ∘ g) ∘ h) = reassoc (f ∘ g ∘ h)


  {-# TERMINATING #-}
  reassoc-correct : Correct reassoc
  reassoc-correct (var f) = C.≈.refl
  reassoc-correct id = C.≈.refl
  reassoc-correct (var f ∘ g) = C.∘-resp-r (reassoc-correct g)
  reassoc-correct (id ∘ f) = C.∘-resp-r (reassoc-correct f)
  reassoc-correct ((f ∘ g) ∘ h) = ≈.trans C.assoc (reassoc-correct (f ∘ g ∘ h))


  simpId : Method
  simpId (var x) = var x
  simpId id = id
  simpId (f ∘ g) with simpId f | simpId g
  ... | var f′  | var g′  = var f′ ∘ var g′
  ... | var f′  | id      = var f′
  ... | var f′  | g′ ∘ g″ = var f′ ∘ g′ ∘ g″
  ... | id      | g′      = g′
  ... | f′ ∘ f″ | var g′  = f′ ∘ f″ ∘ var g′
  ... | f′ ∘ f″ | id      = f′ ∘ f″
  ... | f′ ∘ f″ | g′ ∘ g″ = f′ ∘ f″ ∘ g′ ∘ g″


  simpId-correct : Correct simpId

  simpId-≡ : ∀ {A B} t {u : Tm A B} → simpId t ≡ u → ⟦ t ⟧ C.≈ ⟦ u ⟧


  simpId-correct (var x) = C.≈.refl
  simpId-correct id = C.≈.refl
  simpId-correct (f ∘ g)
    with simpId f | inspect simpId f | simpId g | inspect simpId g
  ... | var f′ | [ eq-f ] | var g′  | [ eq-g ]
      = C.∘-resp (simpId-≡ f eq-f) (simpId-≡ g eq-g)
  ... | var f′ | [ eq-f ] | id      | [ eq-g ]
      = ≈.trans (C.∘-resp (simpId-≡ f eq-f) (simpId-≡ g eq-g)) C.id-r
  ... | var f′ | [ eq-f ] | g′ ∘ g″ | [ eq-g ]
      = C.∘-resp (simpId-≡ f eq-f) (simpId-≡ g eq-g)
  ... | id | [ eq-f ] | g' | [ eq-g ]
      = ≈.trans (C.∘-resp (simpId-≡ f eq-f) (simpId-≡ g eq-g)) C.id-l
  ... | f′ ∘ f″ | [ eq-f ] | var x   | [ eq-g ]
      = ≈.trans (C.∘-resp (simpId-≡ f eq-f) (simpId-≡ g eq-g)) C.assoc
  ... | f′ ∘ f″ | [ eq-f ] | id      | [ eq-g ]
      = ≈.trans (C.∘-resp (simpId-≡ f eq-f) (simpId-≡ g eq-g)) C.id-r
  ... | f′ ∘ f″ | [ eq-f ] | g′ ∘ g″ | [ eq-g ]
      = ≈.trans (C.∘-resp (simpId-≡ f eq-f) (simpId-≡ g eq-g)) C.assoc


  simpId-≡ t eq
      = ≈.trans (simpId-correct t) (≈.reflexive (≡.cong ⟦_⟧ eq))


  simp : Method
  simp = reassoc ⊚ simpId


  simp-correct : Correct simp
  simp-correct
      = ⊚-correct reassoc simpId reassoc-correct simpId-correct


  simp-injective : ∀ {A B} (t u : Tm A B)
    → ⟦ simp t ⟧ C.≈ ⟦ simp u ⟧
    → ⟦ t ⟧ C.≈ ⟦ u ⟧
  simp-injective = Correct→Injective simp simp-correct


  simp-injective′ : ∀ {A B} (t u : Tm A B)
    → simp t ≡ simp u
    → ⟦ t ⟧ C.≈ ⟦ u ⟧
  simp-injective′ t u eq = simp-injective t u (≈.reflexive (≡.cong ⟦_⟧ eq))


reify : Term → Term
reify (def (quote Category.id)
  (argH _ ∷ argH _ ∷ argH _ ∷ argD C ∷ argH _ ∷ []))
    = con (quote id) []
reify (def (quote Category._∘_)
  (argH _ ∷ argH _ ∷ argH _ ∷ argD C ∷ argH _ ∷ argH _ ∷ argH _ ∷ argD f ∷ argD g ∷ []))
    = con (quote _∘_) (argD (reify f) ∷ argD (reify g) ∷ [])
reify t = con (quote Tm.var) (argD t ∷ [])


matchGoal : Term → TC (Term × Term)
matchGoal (def (quote Category._≈_)
  (argH _ ∷ argH _ ∷ argH _ ∷ argD C ∷ argH A ∷ argH B ∷ argD f ∷ argD g ∷ []))
    = return (reify f , reify g)
matchGoal _ = typeError (strErr "matchGoal: not an equality" ∷ [])


macro
  simp! : ∀ {lo la l≈} → Category lo la l≈ → Term → TC ⊤
  simp! C hole = do
      goal ← inferType hole
      blockOnAnyMeta goal
      (lhs , rhs) ← matchGoal goal
      C′ ← quoteTC C
      let solution
            = def (quote simp-injective′)
            ( argD C′
            ∷ argD lhs
            ∷ argD rhs
            ∷ argD (con (quote ≡.refl) [])
            ∷ [])
      unify hole solution


module Test {lo la l≈} {C : Category lo la l≈} (let module C = Category C) {A B C′ D} {f : C′ C.⇒ D} {g : B C.⇒ C′} {h : A C.⇒ B} where

  test : ((C.id C.∘ f) C.∘ g) C.∘ h C.≈ C.id C.∘ f C.∘ g C.∘ h
  test = simp! C
