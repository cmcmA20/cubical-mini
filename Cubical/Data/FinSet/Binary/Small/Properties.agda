{-# OPTIONS --safe --postfix-projections #-}

module Cubical.Data.FinSet.Binary.Small.Properties where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.FinSet.Binary.Small.Base

open import Cubical.Data.Bool
import Cubical.Data.FinSet.Binary.Large as FS
open FS using (isBinary)

module @0 _ where
  open import Cubical.Foundations.Univalence.Universe Binary El (λ _ _ _ → un _ _ _) (λ _ → refl) public

private
  variable
    ℓ : Level
    B : Type ℓ

@0 isBinaryEl : ∀ b → isBinary (El b)
isBinaryEl ℕ₂ = ∣ idEquiv Bool ∣₁
isBinaryEl (un b c e i)
  = squash₁
      (transp (λ j → ∥ Bool ≃ ua e (i ∧ j) ∥₁) (~ i) (isBinaryEl b))
      (transp (λ j → ∥ Bool ≃ ua e (i ∨ ~ j) ∥₁) i (isBinaryEl c))
      i

@0 isBinaryEl' : ∀ ℓ b → isBinary (Lift {j = ℓ} (El b))
isBinaryEl' ℓ ℕ₂ = ∣ LiftEquiv ∣₁
isBinaryEl' ℓ (un b c e i)
  = squash₁
      (transp (λ j → ∥ Bool ≃ Lift {j = ℓ} (ua e (i ∧ j)) ∥₁) (~ i) (isBinaryEl' ℓ b))
      (transp (λ j → ∥ Bool ≃ Lift {j = ℓ} (ua e (i ∨ ~ j)) ∥₁) i (isBinaryEl' ℓ c))
      i

@0 isPropIsSetEl : isOfHLevelDep 1 (λ b → isSet (El b))
isPropIsSetEl = isOfHLevel→isOfHLevelDep 1 (λ b → isPropIsSet)

@0 isSetEl : ∀ b → isSet (El b)
isSetEl ℕ₂ = isSetBool
isSetEl (un b c e i)
  = isPropIsSetEl (isSetEl b) (isSetEl c) (un b c e) i

@0 isGroupoidBinary : isGroupoid Binary
isGroupoidBinary b c = isOfHLevelRetract 2 fun inv leftInv sub
  where
  open Iso (pathIso b c)
  sub : isSet (El b ≡ El c)
  sub = isOfHLevel≡ 2 (isSetEl b) (isSetEl c)

module @0 Reflection where
  bigger : Binary → FS.Binary _
  bigger b = El b , isBinaryEl b

  open Iso

  lemma : ∀(B : Type₀) → ∥ Bool ≃ B ∥₁ → Σ[ b ∈ Binary ] El b ≃ B
  lemma B = rec Sprp (_,_ ℕ₂)
    where
    Fprp : isProp (fiber El B)
    Fprp = isEmbedding→hasPropFibers isEmbeddingEl B

    Sprp : isProp (Σ[ b ∈ Binary ] El b ≃ B)
    Sprp = isOfHLevelRetract 1 (map-snd ua) (map-snd pathToEquiv)
             (λ{ (A , e) → ΣPathP (refl , pathToEquiv-ua e) }) Fprp

  smaller : FS.Binary ℓ-zero → Binary
  smaller (B , tp) = lemma B tp .fst

  bigger-smaller : ∀ p → bigger (smaller p) ≡ p
  bigger-smaller (B , tp)
    = ΣPathP (b≡B , ∥∥-isPropDep (λ B → Bool ≃ B) (isBinaryEl b) tp b≡B)
    where
    b = smaller (B , tp)
    b≡B = ua (lemma B tp .snd)

  smaller-bigger : ∀ b → smaller (bigger b) ≡ b
  smaller-bigger b = equivIso _ _ .inv (lemma (El b) (isBinaryEl b) .snd)

  reflectIso : Iso Binary (FS.Binary ℓ-zero)
  reflectIso .fun = bigger
  reflectIso .inv = smaller
  reflectIso .rightInv = bigger-smaller
  reflectIso .leftInv = smaller-bigger

@0 reflect : Binary ≃ FS.Binary ℓ-zero
reflect = isoToEquiv Reflection.reflectIso

@0 structureᵤ : FS.BinStructure Binary
structureᵤ = λ where
    .base → bs .base .lower
    .loop i → bs .loop i .lower
    .loop² i j → bs .loop² i j .lower
    .trunc → isGroupoidBinary
  where
  open FS.BinStructure

  path : Lift Binary ≡ FS.Binary _
  path = ua (compEquiv (invEquiv LiftEquiv) reflect)

  bs : FS.BinStructure (Lift Binary)
  bs = subst⁻ FS.BinStructure path FS.structure₀
