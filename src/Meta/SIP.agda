{-# OPTIONS --safe #-}
module Meta.SIP where

open import Meta.Prelude

open import Foundations.Univalence.SIP public

open import Meta.Effect.Alt
open import Meta.Literals.FromNat
open import Meta.Literals.FromProduct
open import Meta.Literals.FromString
open import Meta.Reflection.Base

open import Structures.Base public

open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Nat.Base
open import Data.Reflection.Argument
open import Data.Reflection.Instances.FromString
open import Data.Reflection.Name
open import Data.Reflection.Term
open import Data.Unit.Base


private variable
  ℓ ℓ₁ : Level
  S T : Type ℓ → Type ℓ₁

data Str-term ℓ : (ℓ₁ : Level) → (Type ℓ → Type ℓ₁) → Typeω where
  s-const : ∀ {ℓ₁} (A : Type ℓ₁) → Str-term ℓ ℓ₁ (λ _ → A)
  s∙ : Str-term ℓ ℓ id

  _s→_ : ∀ {ℓ₁ ℓ₂} {S} {T} → Str-term ℓ ℓ₁ S → Str-term ℓ ℓ₂ T
       → Str-term ℓ (ℓ₁ ⊔ ℓ₂) (λ X → S X → T X)
  _s×_ : ∀ {ℓ₁ ℓ₂} {S} {T} → Str-term ℓ ℓ₁ S → Str-term ℓ ℓ₂ T
       → Str-term ℓ (ℓ₁ ⊔ ℓ₂) (λ X → S X × T X)

infixr 30 _s→_ _s×_

term→structure : (s : Str-term ℓ ℓ₁ S) → Structure ℓ₁ S
term→action : (s : Str-term ℓ ℓ₁ S) → Equiv-action S

term→structure (s-const x) = constant-str x
term→structure s∙ = pointed-str
term→structure (s₁ s→ s₂) = function-str (term→action s₁) (term→structure s₂)
term→structure (s₁ s× s₂) = product-str (term→structure s₁) (term→structure s₂)

term→action (s-const x₁) x = refl
term→action s∙ x = x
term→action (s₁ s→ s₂) = function-action (term→action s₁) (term→action s₂)
term→action (s₁ s× s₂) = product-action (term→action s₁) (term→action s₂)

@0 term→structure-is-univalent : (s : Str-term ℓ ℓ₁ S) → is-univalent (term→structure s)
@0 term→action-is-transport : (s : Str-term ℓ ℓ₁ S) → is-transport-str (term→action s)

term→structure-is-univalent (s-const x) = constant-str-is-univalent
term→structure-is-univalent s∙ = pointed-str-is-univalent
term→structure-is-univalent (s₁ s→ s₂) =
  function-str-is-univalent
    (term→action s₁) (term→action-is-transport s₁)
    (term→structure s₂) (term→structure-is-univalent s₂)
term→structure-is-univalent (s₁ s× s₂) =
  product-str-is-univalent {σ = term→structure s₁} {τ = term→structure s₂}
    (term→structure-is-univalent s₁) (term→structure-is-univalent s₂)

term→action-is-transport (s-const x) = constant-action-is-transport
term→action-is-transport s∙ = id-action-is-transport
term→action-is-transport (s₁ s→ s₂) =
  function-action-is-transport {α = term→action s₁} {β = term→action s₂}
    (term→action-is-transport s₁) (term→action-is-transport s₂)
term→action-is-transport (s₁ s× s₂) =
  product-action-is-transport {α = term→action s₁} {β = term→action s₂}
    (term→action-is-transport s₁) (term→action-is-transport s₂)

record Desc ℓ ℓ₁ S ax : Typeω where
  field
    descriptor : Str-term ℓ ℓ₁ S

    axioms : ∀ X → S X → Type ax
    axioms-prop : ∀ X s → is-prop (axioms X s)

desc→family : ∀ {ax} → Desc ℓ ℓ₁ S ax → Type ℓ → Type (ℓ₁ ⊔ ax)
desc→family {S} desc X = Σ[ S ꞉ S X ] (desc .Desc.axioms _ S)

desc→structure : ∀ {ax} → (S : Desc ℓ ℓ₁ S ax) → Structure _ (desc→family S)
desc→structure desc = axiom-str (term→structure descriptor) axioms where open Desc desc

@0 desc→is-univalent : ∀ {ax} → (S : Desc ℓ ℓ₁ S ax) → is-univalent (desc→structure S)
desc→is-univalent desc =
  axiom-str-univalent
    (term→structure descriptor) axioms
    (term→structure-is-univalent descriptor) (λ {X} {s} → axioms-prop X s)
  where open Desc desc


make-auto-str-term : ℕ → Term → TC ⊤
make-auto-str-term zero t = type-error "autoDesc ran out of fuel"
make-auto-str-term (suc n) t =
  try-point
    <|> try-bin (quote _s→_)
    <|> try-bin (quote _s×_)
    <|> use-const
  where
    try-point = unify t (con (quote s∙) [])

    try-bin : Name → TC ⊤
    try-bin namen = do
      h₁ ← new-meta unknown
      h₂ ← new-meta unknown
      tt ← unify (con namen (h₁ v∷ h₂ v∷ [])) t
      tt ← make-auto-str-term n h₁
      make-auto-str-term n h₂

    use-const = unify t (con (quote s-const) (unknown v∷ []))

macro
  auto-str-term! : Term → TC ⊤
  auto-str-term! = make-auto-str-term 100
