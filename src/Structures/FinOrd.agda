{-# OPTIONS --safe #-}
module Structures.FinOrd where

open import Foundations.Base
open import Foundations.Sigma
open import Foundations.Univalence

open import Meta.Record
open import Meta.Search.HLevel
open import Meta.Underlying

open import Correspondences.Finite.ManifestBishop

open import Data.Fin.Computational.Base
open import Data.Nat.Base

private variable
  ℓ : Level
  A : Type ℓ

record FinOrd (ℓ : Level) : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor fin-ord
  field
    carrier : Type ℓ
    has-manifest-bishop-finite : Manifest-bishop-finite carrier

open FinOrd

unquoteDecl fin-ord-iso = declare-record-iso fin-ord-iso (quote FinOrd)

instance
  Underlying-FinOrd : Underlying (FinOrd ℓ)
  Underlying-FinOrd {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-FinOrd .⌞_⌟⁰ = carrier

@0 FinOrd≃ℕ : FinOrd ℓ ≃ ℕ
FinOrd≃ℕ {ℓ} =
  FinOrd ℓ                                       ≃⟨ iso→equiv fin-ord-iso ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Manifest-bishop-finite X         ≃⟨ Σ-ap-snd (λ _ → iso→equiv manifest-bishop-finite-iso) ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Σ[ n ꞉ ℕ ] (X ≃ Fin n)           ≃⟨ Σ-ap-snd (λ _ → Σ-ap-snd λ _ → inv-≃ ∙ₑ whisker-lₑ (lift-equiv ₑ⁻¹)) ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Σ[ n ꞉ ℕ ] (Lift ℓ (Fin n) ≃ X)  ≃⟨ Σ-swap ⟩
  Σ[ n ꞉ ℕ ] Σ[ X ꞉ 𝒰 ℓ ] (Lift ℓ (Fin n) ≃ X)  ≃⟨ Σ-contract-snd (λ _ → equiv-is-contr _) ⟩
  ℕ                                              ≃∎

instance
  @0 H-Level-FinOrd : ∀ {n} → H-Level (2 + n) (FinOrd ℓ)
  H-Level-FinOrd = hlevel-basic-instance 2 (is-of-hlevel-≃ 2 FinOrd≃ℕ hlevel!)
