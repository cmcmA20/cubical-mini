{-# OPTIONS --safe #-}
module Structures.Fibration where

open import Foundations.Base

open import Meta.SIP
open import Meta.Underlying

module _ {ℓᵇ} (B : Type ℓᵇ) (ℓ : Level) where
  -- `X` is fibered over `B`
  Fibered : Type ℓ → Type _
  Fibered X = X → B

  private
    fibration-str-term : Str-term _ (ℓᵇ ⊔ ℓ) Fibered
    fibration-str-term = auto-str-term!

  fibration-str : Structure (ℓᵇ ⊔ ℓ) Fibered
  fibration-str = term→structure fibration-str-term

  @0 fibration-str-is-univalent : is-univalent fibration-str
  fibration-str-is-univalent = term→structure-is-univalent fibration-str-term

  Fibration : Type (ℓᵇ ⊔ ℓsuc ℓ)
  Fibration = Type-with fibration-str

  @0 _ : {U@(X , f) V@(Y , g) : Fibration} {e : X ≃ Y}
       →  fibration-str .is-hom U V e
       ＝ Π[ x ꞉ X ] (f x ＝ g (e # x))
  _ = refl
