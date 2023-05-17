{-# OPTIONS --safe #-}
module Structures.Function where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Pi.Properties
open import Foundations.Univalence

private variable
  ℓ ℓ₁ ℓ₂ : Level
  A : Type ℓ
  S T : Type ℓ → Type ℓ₁

Str-function-str : Structure ℓ₁ S → Structure ℓ₂ T → Structure _ (λ X → S X → T X)
Str-function-str {S} σ τ .is-hom (A , f) (B , g) h =
  {s : S A} {t : S B} → σ .is-hom (A , s) (B , t) h
                      → τ .is-hom (A , f s) (B , g t) h

@0 Str-function-str-is-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                                 → is-univalent σ → is-univalent τ
                                 → is-univalent (Str-function-str σ τ)
Str-function-str-is-univalent {S} {T} {σ} {τ} θ₁ θ₂ eqv =
  Π-impl-cod-≃ (λ s → Π-impl-cod-≃ λ t → function-≃ (θ₁ eqv) (θ₂ eqv)) ∙ₑ funext-dep-≃

-- prefer this one
Function-str : Equiv-action S → Structure ℓ T → Structure _ (λ X → S X → T X)
Function-str {S} act str .is-hom (A , f) (B , g) e =
  Π[ s ꞉ S A ] str .is-hom (A , f s) (B , g (act e .fst s)) e

@0 Function-str-is-univalent
  : (α : Equiv-action S) → is-transport-str α
  → (τ : Structure ℓ T) → is-univalent τ
  → is-univalent (Function-str α τ)
Function-str-is-univalent {S} {T} α α-tr τ τ-univ {X , f} {Y , g} eqv =
  ((s : S X) → τ .is-hom (X , f s) (Y , _) eqv)     ≃⟨ Π-cod-≃ (λ s → τ-univ eqv ∙ₑ path→Equiv (ap (PathP (λ i → T (ua eqv i)) (f s) ∘ g) (α-tr _ _))) ⟩
  ((s : S X) → PathP (λ i → T (ua eqv i)) (f s) _)  ≃⟨ (hetero-homotopy≃homotopy ₑ⁻¹) ∙ₑ funext-dep-≃ ⟩
  _                                                 ≃∎

Function-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X → T X)
Function-action actx acty eqv = function-≃ (actx eqv) (acty eqv)

@0 Function-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (Function-action α β)
Function-action-is-transport {S} {α} {β} α-tr β-tr eqv f =
  fun-ext λ x → ap (β eqv .fst ∘ f) (sym-transport-str α α-tr eqv x)
              ∙ β-tr eqv (f (subst S (sym (ua eqv)) x))
