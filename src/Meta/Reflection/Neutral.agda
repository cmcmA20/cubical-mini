{-# OPTIONS --safe #-}
module Meta.Reflection.Neutral where

open import Foundations.Base

open import Correspondences.Binary.Transitive

open import Data.Empty.Base
open import Data.List.Base
open import Data.List.Instances.Append
open import Data.Reflection.Abs
open import Data.Reflection.Argument
open import Data.Reflection.Error
open import Data.Reflection.Fixity
open import Data.Reflection.Literal
open import Data.Reflection.Meta
open import Data.Reflection.Name
open import Data.Reflection.Term

-- Notation class for the reflected in reflected syntax which have a
-- notion of neutrals, for which application is cheap. This is used to
-- support the _##_ family of operators.
record Has-neutrals {ℓ} (A : Type ℓ) : Type (ℓsuc ℓ) where
  field
    neutral : A → Type ℓ
    applyⁿᵉ : (d : A) ⦃ _ : neutral d ⦄ (arg : List (Arg A)) → A

open Has-neutrals ⦃ ... ⦄ using (applyⁿᵉ) public

module _ {ℓ} {A : Type ℓ} ⦃ a : Has-neutrals A ⦄ (d : A) ⦃ _ : Has-neutrals.neutral a d ⦄ where
  infixl 20 _##_ _##ₙ_ _##ᵢ_ _##ₕ_ _##ₙ₀_ _##ᵢ₀_ _##ₕ₀_

  -- Apply a neutral to an argument with specified information.
  _##_ : (arg : Arg A) → A
  _##_ x = Has-neutrals.applyⁿᵉ a d (x ∷ [])

  -- Apply a neutral to an argument with the default information.
  _##ₙ_ : (arg : A) → A
  _##ₙ_ x = _##_ (argN x)

  -- Apply a neutral to an instance argument with the default modality.
  _##ᵢ_ : (arg : A) → A
  _##ᵢ_ x = _##_ (argI x)

  -- Apply a neutral to a hidden argument with the default modality.
  _##ₕ_ : (arg : A) → A
  _##ₕ_ x = _##_ (argH x)

  -- Apply a neutral to an argument with erased modality.
  _##ₙ₀_ : (arg : A) → A
  _##ₙ₀_ x = _##_ (argN0 x)

  -- Apply a neutral to an instance argument with erased modality.
  _##ᵢ₀_ : (arg : A) → A
  _##ᵢ₀_ x = _##_ (argI0 x)

  -- Apply a neutral to a hidden argument with erased modality.
  _##ₕ₀_ : (arg : A) → A
  _##ₕ₀_ x = _##_ (argH0 x)

instance
  Has-neutrals-Term : Has-neutrals Term
  Has-neutrals-Term = record { neutral = neutral ; applyⁿᵉ = apply } where
    neutral : Term → Type
    neutral (def _ _)     = ⊤
    neutral (con _ _)     = ⊤
    neutral (meta _ _)    = ⊤
    neutral (var _ _)     = ⊤
    neutral (pat-lam _ _) = ⊤
    neutral _             = ⊥

    apply : (d : Term) ⦃ _ : neutral d ⦄ (arg : Args) → Term
    apply (def v as)      a = def v  (as <> a)
    apply (con v as)      a = con v  (as <> a)
    apply (meta m as)     a = meta m (as <> a)
    apply (var v as)      a = var v  (as <> a)
    apply (pat-lam cs as) a = pat-lam cs (as <> a)

  Has-neutrals-Pattern : Has-neutrals Pattern
  Has-neutrals-Pattern = record { neutral = neutral ; applyⁿᵉ = apply } where
    neutral : Pattern → Type
    neutral (con _ _) = ⊤
    neutral _ = ⊥

    apply : (d : Pattern) ⦃ _ : neutral d ⦄ (arg : Patterns) → Pattern
    apply (con c ps) a = con c (ps <> a)
