{-# OPTIONS --safe #-}
module Structures.Fibration where

open import Foundations.Base

open import Meta.SIP

open import Functions.Fibration

private variable
  ℓᵇ : Level

module _ (B : Type ℓᵇ) (ℓ : Level) where

  Fibered : Type ℓ → Type _
  Fibered X = X → B

  private
    fibration-str-term : Str-term _ (ℓᵇ ⊔ ℓ) Fibered
    fibration-str-term = auto-str-term!

  fibration-str : Structure (ℓᵇ ⊔ ℓ) Fibered
  fibration-str = Term→structure fibration-str-term

  @0 fibration-str-is-univalent : is-univalent fibration-str
  fibration-str-is-univalent = Term→structure-is-univalent fibration-str-term

  Fibration : Type (ℓᵇ ⊔ ℓsuc ℓ)
  Fibration = Type-with fibration-str

  module _ {U@(X , f) V@(Y , g) : Fibration}
           {e : X ≃ Y} {p : f ＝ g ∘ e .fst} where private
    @0 observe : U ＝ V
    observe = sip fibration-str-is-univalent (e , happly p)
