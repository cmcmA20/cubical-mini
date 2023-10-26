{-# OPTIONS --safe #-}
module Algebra.Magma where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Record
open import Meta.SIP
open import Meta.Search.HLevel

open import Structures.n-Type

private variable
  ℓ : Level
  A : Type ℓ
  _✦_ : A → A → A

-- untruncated magmas

∞-Magma-on : Type ℓ → Type ℓ
∞-Magma-on X = X → X → X

private
  ∞-magma-str-term : Str-term ℓ ℓ ∞-Magma-on
  ∞-magma-str-term = auto-str-term!

∞-magma-str : Structure ℓ ∞-Magma-on
∞-magma-str = term→structure ∞-magma-str-term

@0 ∞-magma-str-is-univalent : is-univalent (∞-magma-str {ℓ})
∞-magma-str-is-univalent = term→structure-is-univalent ∞-magma-str-term

∞-Magma : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
∞-Magma _ = Type-with ∞-magma-str


-- n-truncated magmas

record is-n-magma (n : HLevel) {A : 𝒰 ℓ} (_⋆_ : A → A → A) : 𝒰 ℓ where
  no-eta-equality
  field instance has-is-of-hlevel : is-of-hlevel n A

unquoteDecl is-n-magma-iso = declare-record-iso is-n-magma-iso (quote is-n-magma)

private variable n : HLevel

is-magma : (A → A → A) → Type _
is-magma = is-n-magma 2

is-2-magma : (A → A → A) → Type _
is-2-magma = is-n-magma 3

instance
  is-n-magma-is-prop : is-prop (is-n-magma n _✦_)
  is-n-magma-is-prop = is-of-hlevel-≃ 1 (iso→equiv is-n-magma-iso) hlevel!

is-n-magma-is-of-hlevel : (k : HLevel) → is-of-hlevel (suc k) (is-n-magma n _✦_)
is-n-magma-is-of-hlevel _ = is-prop→is-of-hlevel-suc is-n-magma-is-prop

instance
  decomp-hlevel-n-magma : goal-decomposition (quote is-of-hlevel) (is-n-magma n _✦_)
  decomp-hlevel-n-magma = decomp (quote is-n-magma-is-of-hlevel ) (`level-minus 1 ∷ [])

module _ (n : HLevel) where
  n-Magma-on : Type ℓ → Type ℓ
  n-Magma-on X = Σ[ _⋆_ ꞉ (X → X → X) ] (is-n-magma n _⋆_)

  private
    n-magma-desc : Desc ℓ ℓ ∞-Magma-on ℓ
    n-magma-desc .Desc.descriptor = auto-str-term!
    n-magma-desc .Desc.axioms _ = is-n-magma n
    n-magma-desc .Desc.axioms-prop _ _ = is-n-magma-is-prop

  n-magma-str : Structure ℓ _
  n-magma-str = desc→structure n-magma-desc

  @0 n-magma-str-is-univalent : is-univalent (n-magma-str {ℓ})
  n-magma-str-is-univalent = desc→is-univalent n-magma-desc


n-Magma : (ℓ : Level) (n : HLevel) → 𝒰 (ℓsuc ℓ)
n-Magma _ n = Type-with (n-magma-str n)

2-Magma : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
2-Magma ℓ = n-Magma ℓ 2

3-Magma : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
3-Magma ℓ = n-Magma ℓ 3

-- Observe that homomorphism of n-magmas is exactly
-- binary operation preservation
module _ {A* B* : n-Magma ℓ n} {e : ⌞ A* ⌟ ≃ ⌞ B* ⌟} where private
  _⋆_ = A* .snd .fst
  _☆_ = B* .snd .fst
  module e = Equiv e

  _ :  n-magma-str n .is-hom A* B* e
    ＝ Π[ x ꞉ ⌞ A* ⌟ ] Π[ y ꞉ ⌞ A* ⌟ ] (e.to (x ⋆ y) ＝ e.to x ☆ e.to y)
  _ = refl
