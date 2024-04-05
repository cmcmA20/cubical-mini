{-# OPTIONS --safe #-}
module Structures.FinOrd where

open import Meta.Prelude

open import Meta.Projection
open import Meta.Record
open import Meta.Reflection.Base

open import Structures.n-Type

open import Correspondences.Finite.ManifestBishop

open import Data.Bool.Base
open import Data.Fin.Computational.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Path

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
  H-Level-FinOrd = hlevel-basic-instance 2 $ ≃→is-of-hlevel! 2 (equivᴱ≃equiv $ FinOrd≃ᴱℕ)

  mbf-proj-fin-ord : Struct-proj-desc false (quote carrier)
  mbf-proj-fin-ord .Struct-proj-desc.has-level = quote has-manifest-bishop-finite
  mbf-proj-fin-ord .Struct-proj-desc.get-argument (_ ∷ x v∷ []) = pure x
  mbf-proj-fin-ord .Struct-proj-desc.get-argument _ = type-error []

  mbf-projection
    : ∀ {ℓ} {A : Type ℓ}
    → {@(tactic struct-proj A nothing) A-mbf : Manifest-bishop-finite A}
    → Manifest-bishop-finite A
  mbf-projection {A-mbf} = A-mbf
  {-# INCOHERENT mbf-projection #-}


-- Usage
module _ {ℓᵃ ℓᵇ : Level} {A : FinOrd ℓᵃ} {B : A →̇ FinOrd ℓᵇ} where private
  open import Correspondences.Discrete
  open import Correspondences.Exhaustible
  open import Correspondences.Omniscient

  _ : is-groupoid (A →̇ A)
  _ = hlevel!

  _ : is-discrete (A ×̇ A)
  _ = auto

  _ : Manifest-bishop-finite (A →̇ A →̇ A)
  _ = auto

  _ : Omniscient Π[ B ]
  _ = autoω

  _ : Omniscient₁ (A ×̇ Π[ B ])
  _ = autoω

  _ : Exhaustible (A ×̇ A)
  _ = autoω
