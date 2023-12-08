{-# OPTIONS --safe #-}
module Structures.FinSet where

open import Foundations.Base
open import Foundations.Sigma
open import Foundations.Univalence

open import Meta.Effect.Bind
open import Meta.Record
open import Meta.Search.HLevel
open import Meta.SIP
open import Meta.Underlying public

open import Structures.IdentitySystem.Interface

open import Correspondences.Finite.Bishop

open import Data.Fin.Computational.Base
open import Data.Nat.Base
open import Data.Nat.Path

open import Truncation.Propositional as ∥-∥₁
open import Truncation.Set as ∥-∥₂

private variable
  ℓ : Level
  A : Type ℓ

record FinSet (ℓ : Level) : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor fin-set
  field
    carrier : Type ℓ
    has-is-bishop-finite : is-bishop-finite carrier

open FinSet

unquoteDecl fin-set-iso = declare-record-iso fin-set-iso (quote FinSet)

instance
  Underlying-FinSet : Underlying (FinSet ℓ)
  Underlying-FinSet {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-FinSet .⌞_⌟⁰ = carrier


-- have to go through sigmas
private
  fin-set′-desc : Desc ℓ _ (λ X → ℕ) ℓ
  fin-set′-desc .Desc.descriptor = auto-str-term!
  fin-set′-desc .Desc.axioms X n = ∥ X ≃ Fin n ∥₁
  fin-set′-desc .Desc.axioms-prop = hlevel!

  fin-set′-str : Structure {ℓ₁ = ℓ} 0ℓ _
  fin-set′-str = desc→structure fin-set′-desc

  @0 fin-set-str-is-univalent : is-univalent {_} {ℓ} fin-set′-str
  fin-set-str-is-univalent = desc→is-univalent fin-set′-desc

  FinSet′ : (ℓ : Level) → Type (ℓsuc ℓ)
  FinSet′ _ = Type-with fin-set′-str

  @0 fin-set′-ext : {X Y : FinSet′ ℓ} → (X .snd .fst ＝ Y .snd .fst) → ∥ X ＝ Y ∥₁
  fin-set′-ext {X} {Y} p = do
    u ← X .snd .snd
    v ← Y .snd .snd
    pure $ sip fin-set-str-is-univalent (u ∙ₑ path→equiv (ap (λ n → Fin n) p) ∙ₑ v ₑ⁻¹ , p)

  @0 ∥FinSet′∥₂≃ℕ : ∥ FinSet′ ℓ ∥₂ ≃ ℕ
  ∥FinSet′∥₂≃ℕ = iso→equiv $ to , iso from (λ _ → refl) li where
    to : _
    to = ∥-∥₂.rec! (fst ∘ snd)

    from : _
    from n = ∣ Lift _ (Fin n) , n , ∣ lift-equiv ∣₁ ∣₂

    li : from is-left-inverse-of to
    li = ∥-∥₂.elim! λ _ → ∥-∥₂-path.from (fin-set′-ext refl)

@0 ∥FinSet∥₂≃ℕ : ∥ FinSet ℓ ∥₂ ≃ ℕ
∥FinSet∥₂≃ℕ = apₑ ∥_∥₂ (iso→equiv fin-set-iso ∙ₑ Σ-ap-snd λ X → iso→equiv is-bishop-finite-iso) ∙ₑ ∥FinSet′∥₂≃ℕ
