{-# OPTIONS --safe #-}
module Structures.FinSet where

open import Foundations.Base
open import Foundations.Erased
open import Foundations.Sigma
open import Foundations.Univalence

open import Meta.Effect.Bind
open import Meta.Record
open import Meta.Search.HLevel
open import Meta.SIP
open import Meta.Variadic

open import Structures.IdentitySystem.Interface
open import Structures.n-Type

open import Correspondences.Discrete
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

@0 FinSet-is-groupoid : is-groupoid (FinSet ℓ)
FinSet-is-groupoid = is-of-hlevel-≃ 3 go hlevel! where
  go = FinSet _
         ≃⟨ iso→equiv fin-set-iso ⟩
       Σ[ X ꞉ Type _ ] is-bishop-finite X
         ≃⟨ Σ-ap-snd (λ _ → prop-extₑ! < is-discrete→is-set ∘ is-bishop-finite→is-discrete , id > snd) ⟩
       Σ[ X ꞉ Type _ ] is-set X × is-bishop-finite X
         ≃⟨ Σ-assoc ⟩
       Σ[ U ꞉ Σ[ X ꞉ Type _ ] is-set X ] is-bishop-finite (U .fst)
         ≃˘⟨ Σ-ap-fst (iso→equiv n-Type-iso) ⟩
       Σ[ X ꞉ Set _ ] is-bishop-finite ⌞ X ⌟ ≃∎

instance
  @0 H-Level-FinSet : ∀ {n} → H-Level (3 + n) (FinSet ℓ)
  H-Level-FinSet = hlevel-basic-instance 3 FinSet-is-groupoid

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

  ∥FinSet′∥₂≃ᴱℕ : ∥ FinSet′ ℓ ∥₂ ≃ᴱ ℕ
  ∥FinSet′∥₂≃ᴱℕ = (∥-∥₂.rec! (fst ∘ snd)) , is-isoᴱ→is-equivᴱ
    ( (λ n → pure $ Lift _ (Fin n) , n , pure lift-equiv)
    , erase (λ _ → refl)
    , erase (∥-∥₂.elim! (λ X → ∥-∥₂-path.from (fin-set′-ext refl))) )

∥FinSet∥₂≃ᴱℕ : ∥ FinSet ℓ ∥₂ ≃ᴱ ℕ
∥FinSet∥₂≃ᴱℕ =
      ∥-∥₂-≃ᴱ (iso→equiv fin-set-iso ∙ₑ Σ-ap-snd λ _ → iso→equiv is-bishop-finite-iso)
  ∙ᴱₑ ∥FinSet′∥₂≃ᴱℕ
