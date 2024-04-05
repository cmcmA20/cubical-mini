{-# OPTIONS --safe #-}
module Structures.FinOrd where

open import Meta.Prelude

open import Meta.Record
open import Meta.Search.HLevel

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

FinOrd≃ᴱℕ : FinOrd ℓ ≃ᴱ ℕ
FinOrd≃ᴱℕ {ℓ} =
  FinOrd ℓ                                       ≃ᴱ⟨ ≃→≃ᴱ (≅→≃ fin-ord-iso) ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Manifest-bishop-finite X         ≃ᴱ⟨ ≃→≃ᴱ (Σ-ap-snd (λ _ → ≅→≃ manifest-bishop-finite-iso)) ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Σ[ n ꞉ ℕ ] (X ≃ Fin n)           ≃ᴱ⟨ ≃→≃ᴱ (Σ-ap-snd (λ _ → Σ-ap-snd λ _ → inv-≃ ∙ whisker-lₑ (lift≃id ⁻¹))) ⟩
  Σ[ X ꞉ 𝒰 ℓ ] Σ[ n ꞉ ℕ ] (Lift ℓ (Fin n) ≃ X)  ≃ᴱ⟨ ≃→≃ᴱ Σ-swap ⟩
  Σ[ n ꞉ ℕ ] Σ[ X ꞉ 𝒰 ℓ ] (Lift ℓ (Fin n) ≃ X)  ≃ᴱ⟨ Σ-contract-sndᴱ (λ n → equiv-is-contrᴱ _) ⟩
  ℕ                                              ≃ᴱ∎

instance
  @0 H-Level-FinOrd : ∀ {n} → H-Level (2 + n) (FinOrd ℓ)
  H-Level-FinOrd = hlevel-basic-instance 2 $ ≃→is-of-hlevel 2 (equivᴱ≃equiv $ FinOrd≃ᴱℕ) hlevel!
