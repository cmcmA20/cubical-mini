{-# OPTIONS --safe #-}
module Meta.SIP where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Univalence.SIP

open import Structures.Base public

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

Term→structure : (s : Str-term ℓ ℓ₁ S) → Structure ℓ₁ S
Term→action : (s : Str-term ℓ ℓ₁ S) → Equiv-action S

Term→structure (s-const x) = Constant-str x
Term→structure s∙ = Pointed-str
Term→structure (s s→ s₁) = Function-str (Term→action s) (Term→structure s₁)
Term→structure (s s× s₁) = Product-str (Term→structure s) (Term→structure s₁)

Term→action (s-const x₁) x = idₑ
Term→action s∙ x = x
Term→action (s s→ s₁) = function-action (Term→action s) (Term→action s₁)
Term→action (s s× s₁) = product-action (Term→action s) (Term→action s₁)

@0 Term→structure-is-univalent : (s : Str-term ℓ ℓ₁ S) → is-univalent (Term→structure s)
@0 Term→action-is-transport : (s : Str-term ℓ ℓ₁ S) → is-transport-str (Term→action s)

Term→structure-is-univalent (s-const x) = constant-str-is-univalent
Term→structure-is-univalent s∙ = pointed-str-is-univalent
Term→structure-is-univalent (s s→ s₁) =
  function-str-is-univalent
    (Term→action s) (Term→action-is-transport s)
    (Term→structure s₁) (Term→structure-is-univalent s₁)
Term→structure-is-univalent (s s× s₁) =
  product-str-is-univalent {σ = Term→structure s} {τ = Term→structure s₁}
    (Term→structure-is-univalent s) (Term→structure-is-univalent s₁)

Term→action-is-transport (s-const x) = constant-action-is-transport
Term→action-is-transport s∙ = id-action-is-transport
Term→action-is-transport (s s→ s₁) =
  function-action-is-transport {α = Term→action s} {β = Term→action s₁}
    (Term→action-is-transport s) (Term→action-is-transport s₁)
Term→action-is-transport (s s× s₁) =
  product-action-is-transport {α = Term→action s} {β = Term→action s₁}
    (Term→action-is-transport s) (Term→action-is-transport s₁)

record Str-desc ℓ ℓ₁ S ax : Typeω where
  field
    descriptor : Str-term ℓ ℓ₁ S

    axioms : ∀ X → S X → Type ax
    axioms-prop : ∀ X s → is-prop (axioms X s)

Desc→Fam : ∀ {ax} → Str-desc ℓ ℓ₁ S ax → Type ℓ → Type (ℓ₁ ⊔ ax)
Desc→Fam {S} desc X =
  Σ[ S ꞉ S X ]
    (desc .Str-desc.axioms _ S)

Desc→Str : ∀ {ax} → (S : Str-desc ℓ ℓ₁ S ax) → Structure _ (Desc→Fam S)
Desc→Str desc = Axiom-str (Term→structure descriptor) axioms
  where open Str-desc desc

@0 Desc→is-univalent : ∀ {ax} → (S : Str-desc ℓ ℓ₁ S ax) → is-univalent (Desc→Str S)
Desc→is-univalent desc =
  Axiom-str-univalent
    (Term→structure descriptor) axioms
    (Term→structure-is-univalent descriptor) (λ {X} {s} → axioms-prop X s)
  where open Str-desc desc
