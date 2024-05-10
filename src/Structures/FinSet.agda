{-# OPTIONS --safe #-}
module Structures.FinSet where

open import Meta.Prelude
open import Meta.Effect.Bind
open import Meta.Projection
open import Meta.Record
open import Meta.Reflection.Base
open import Meta.SIP

open import Structures.n-Type

open import Logic.Discreteness

open import Combinatorics.Finiteness.Bishop

open import Data.Bool.Base
open import Data.Fin.Computational.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Reflection.Argument
open import Data.Truncation.Propositional as ∥-∥₁
open import Data.Truncation.Set as ∥-∥₂

private variable
  ℓ : Level
  A : Type ℓ

record FinSet (ℓ : Level) : Type (ℓsuc ℓ) where
  no-eta-equality
  constructor fin-set
  field
    carrier : Type ℓ
    has-bishop-finite : is-bishop-finite carrier

open FinSet

unquoteDecl fin-set-iso = declare-record-iso fin-set-iso (quote FinSet)

instance
  Underlying-FinSet : Underlying (FinSet ℓ)
  Underlying-FinSet {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-FinSet .⌞_⌟⁰ = carrier

  bf-proj-fin-ord : Struct-proj-desc false (quote carrier)
  bf-proj-fin-ord .Struct-proj-desc.has-level = quote has-bishop-finite
  bf-proj-fin-ord .Struct-proj-desc.get-argument (_ ∷ x v∷ []) = pure x
  bf-proj-fin-ord .Struct-proj-desc.get-argument _ = type-error []

  bf-projection
    : ∀ {ℓ} {A : Type ℓ}
    → {@(tactic struct-proj A nothing) A-bf : is-bishop-finite A}
    → is-bishop-finite A
  bf-projection {A-bf} = A-bf
  {-# INCOHERENT bf-projection #-}


@0 FinSet-is-groupoid : is-groupoid (FinSet ℓ)
FinSet-is-groupoid = ≃→is-of-hlevel 3 go (λ _ _ → hlevel!) where
  go = FinSet _
         ~⟨ ≅→≃ fin-set-iso ⟩
       Σ[ X ꞉ Type _ ] is-bishop-finite X
         ~⟨ Σ-ap-snd (λ _ → prop-extₑ! < (λ bf → is-discrete→is-set (is-bishop-finite→is-discrete ⦃ bf ⦄)) , id > snd) ⟩
       Σ[ X ꞉ Type _ ] is-set X × is-bishop-finite X
         ~⟨ Σ-assoc ⟩
       Σ[ U ꞉ Σ[ X ꞉ Type _ ] is-set X ] is-bishop-finite (U .fst)
         ~⟨ Σ-ap-fst (≅→≃ n-Type-iso) ⟨
       Σ[ X ꞉ Set _ ] is-bishop-finite ⌞ X ⌟
         ∎

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
    pure $ sip fin-set-str-is-univalent (u ∙ =→≃ (ap (λ n → Fin n) p) ∙ v ⁻¹ , p)

  ∥FinSet′∥₂≃ᴱℕ : ∥ FinSet′ ℓ ∥₂ ≃ᴱ ℕ
  ∥FinSet′∥₂≃ᴱℕ {ℓ} = rec! ⦃ Inductive-∥-∥₂ ⦃ Inductive-default ⦄ ⦄ (fst ∘ snd) , is-isoᴱ→is-equivᴱ {B = ℕ}
    ( (λ n → pure $ Lift ℓ (Fin n) , n , pure lift≃id)
    , erase (λ _ → refl)
    , erase (elim! λ X n e → =∘∣-∣₂≃∥-∥₁∘= ⁻¹ $ fin-set′-ext refl) )

∥FinSet∥₂≃ᴱℕ : ∥ FinSet ℓ ∥₂ ≃ᴱ ℕ
∥FinSet∥₂≃ᴱℕ {ℓ} =
  ∥ FinSet  ℓ ∥₂  ~⟨ ≃→≃ᴱ (∥-∥₂.ae (≅→≃ fin-set-iso ∙ Σ-ap-snd λ _ → ≅→≃ is-bishop-finite-iso)) ⟩
  ∥ FinSet′ ℓ ∥₂  ~⟨ ∥FinSet′∥₂≃ᴱℕ ⟩
  ℕ               ∎


-- Usage
module _ {ℓᵃ ℓᵇ : Level} {A : FinSet ℓᵃ} {B : A →̇ FinSet ℓᵇ} where private
  open import Logic.Exhaustibility
  open import Logic.Omniscience

  _ : is-groupoid (A →̇ A)
  _ = hlevel!

  _ : is-discrete (A ×̇ A)
  _ = auto

  _ : is-bishop-finite (A →̇ A →̇ A)
  _ = auto

  _ : Omniscient₁ Π[ B ]
  _ = autoω

  _ : Exhaustible (A ×̇ A)
  _ = autoω

  _ : {x y : ⌞ A ⌟} → is-bishop-finite (x ＝ y)
  _ = auto
