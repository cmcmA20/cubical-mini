{-# OPTIONS --safe #-}
module Meta.Variadic where

open import Foundations.Prelude

open import Data.HVec.Base public
open import Data.Nat.Base

-- Correspondence valued in arbitrary structure
SCorr
  : (arity : ℕ) {ls : Levels arity} (As : Types _ ls)
    {ℓ : Level} (U : Type ℓ) ⦃ u : Underlying U ⦄
  → Type (ℓ ⊔ ℓsup _ ls)
SCorr arity As U = Arrows arity As U

SCorr⁰ = SCorr 0
SCorr¹ = SCorr 1
SCorr² = SCorr 2
SCorr³ = SCorr 3
SCorr⁴ = SCorr 4
SCorr⁵ = SCorr 5

SPred = SCorr¹

-- Type-valued correspondence
Corr
  : (arity : ℕ) {ls : Levels arity} (As : Types _ ls) (ℓ : Level)
  → Type (ℓsuc ℓ ⊔ ℓsup _ ls)
Corr arity As ℓ = SCorr arity As (Type ℓ)

Corr⁰ = Corr 0
Corr¹ = Corr 1
Corr² = Corr 2
Corr³ = Corr 3
Corr⁴ = Corr 4
Corr⁵ = Corr 5

Pred = Corr¹

Variadic¹ : Typeω
Variadic¹ =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U
  → Corr  _ As (u .ℓ-underlying)

Variadic-binding¹ : Typeω
Variadic-binding¹ =
    {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr _ As U
  → Type (u .ℓ-underlying ⊔ ℓsup _ ls)

Quantⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types _ ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → (∀ {ℓᵃ ℓᵇ} (A : Type ℓᵃ) → (A → Type ℓᵇ) → Type (ℓᵃ ⊔ ℓᵇ))
  → SCorr _ As U
  → Type (u .ℓ-underlying ⊔ ℓsup _ ls)
Quantⁿ {0}           Q T = ⌞ T ⌟
Quantⁿ {1}           Q T = Q _ λ x → ⌞ T x ⌟
Quantⁿ {suc (suc _)} Q T = Q _ λ x → Quantⁿ Q (T x)

Universalⁿ : Variadic-binding¹
Universalⁿ = Quantⁿ Π-syntax

IUniversalⁿ : Variadic-binding¹
IUniversalⁿ = Quantⁿ ∀-syntax

Existentialⁿ : Variadic-binding¹
Existentialⁿ = Quantⁿ Σ-syntax

private variable ℓᵃ ℓᵇ ℓᶜ ℓᵈ ℓ ℓ′ ℓ″ : Level

instance
  Refl-Corr² : Refl (λ A B → A → B → 𝒰 ℓ)
  Refl-Corr² .refl = _＝_

  Dual-Corr² : Dual {A = 𝒰 ℓᵃ} {B = 𝒰 ℓᵇ}  (λ A B → A → B → 𝒰 ℓ) (λ A B → A → B → 𝒰 ℓ)
  Dual-Corr² ._ᵒᵖ = flip

  -- TODO generalize to SCorr
  Comp-Corr²
    : Comp {A = 𝒰 ℓᵃ} {B = 𝒰 ℓᵇ} {C = 𝒰 ℓᶜ}
        (λ A B → A → B → 𝒰 ℓ)
        (λ B C → B → C → 𝒰 ℓ′)
        (λ A C → A → C → Type (ℓ ⊔ ℓᵇ ⊔ ℓ′))
  Comp-Corr² ._∙_ {x = A} {y = B} {z = C} R S a c = Σ[ b ꞉ B ] R a b × S b c
  {-# OVERLAPPING Comp-Corr² #-}

  @0 GAssoc-Corr²
    : GAssoc {A = 𝒰 ℓᵃ} {B = 𝒰 ℓᵇ} {C = 𝒰 ℓᶜ} {D = 𝒰 ℓᵈ}
        (λ A B → A → B → 𝒰 ℓ) (λ B C → B → C → 𝒰 ℓ′) (λ C D → C → D → 𝒰 ℓ″)
        _ _ _
  GAssoc-Corr² .∙-assoc {a = A} {b = B} {c = C} {d = D} R S T = fun-ext λ a → fun-ext λ d → ua $
    (Σ[ b ꞉ B ] R a b × (Σ[ c ꞉ C ] S b c × T c d))                ~⟨ Σ-assoc ∙ Σ-swap ⟩
    (Σ[ c ꞉ C ] Σ[ f ꞉ Σ[ b ꞉ B ] R a b ] S (f .fst) c × T c d)    ~⟨ Σ-ap-snd (λ c → Σ-assoc ∙ Σ-ap-fst (Σ-assoc ⁻¹)) ⟩
    (Σ[ c ꞉ C ] (Σ[ b ꞉ B ] R a b × S b c) × T c d)                ∎

  @0 GUnit-i-Corr² : GUnit-i {A = 𝒰 ℓᵃ} (λ A B → A → B → 𝒰 ℓ) (λ B C → B → C → 𝒰 ℓ)
  GUnit-i-Corr² .∙-id-i {x = A} {y = B} R = fun-ext λ a → fun-ext λ b → ua
    $ Σ-ap-snd (λ _ → ×-swap)
    ∙ Σ-assoc
    ∙ Σ-contract-fst (≃→is-of-hlevel 0 (Σ-ap-snd (λ _ → sym-≃)) (singletonₚ-is-contr (b , refl)))

  @0 GUnit-o-Corr² : GUnit-o {A = 𝒰 ℓ} {B = 𝒰 ℓ′} (λ A B → A → B → 𝒰 ℓ) (λ B C → B → C → 𝒰 ℓ)
  GUnit-o-Corr² .∙-id-o {x = A} {y = B} R = fun-ext λ a → fun-ext λ b → ua $
    Σ-assoc ∙ Σ-contract-fst (singletonₚ-is-contr (a , refl))

  Whisker-i-Corr-Fun
    : Whisker-i {A = 𝒰 ℓᵃ} {B = 𝒰 ℓᵇ} {C = 𝒰 ℓᶜ}
        (λ A B → A → B → 𝒰 ℓ)
        (λ B C → B → C → 𝒰 ℓ′) _
        (λ B C → B → C → 𝒰 ℓ″) _
        (λ B C R S → ∀[ R ⇒ S ])
        (λ A C R S → ∀[ R ⇒ S ])
  Whisker-i-Corr-Fun ._◁_ _ α = second $ second $ α
  {-# OVERLAPPING Whisker-i-Corr-Fun #-}

  Whisker-o-Corr-Fun
    : Whisker-o {A = 𝒰 ℓᵃ} {B = 𝒰 ℓᵇ} {C = 𝒰 ℓᶜ}
        (λ A B → A → B → 𝒰 ℓ)
        (λ B C → B → C → 𝒰 ℓ′) _
        (λ B C → B → C → 𝒰 ℓ″) _
        (λ B C R S → ∀[ R ⇒ S ])
        (λ A C R S → ∀[ R ⇒ S ])
  Whisker-o-Corr-Fun ._▷_ α _ = second $ first $ α
  {-# OVERLAPPING Whisker-o-Corr-Fun #-}
