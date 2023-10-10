{-# OPTIONS --safe --overlapping-instances --instance-search-depth=1 #-}
module Algebra.Rig where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel
open import Meta.SIP
open import Meta.Underlying

open import Algebra.Semiring public

private variable
  ℓ     : Level
  A     : Type ℓ
  e x y z u : A
  _✦_ _✧_ : A → A → A

Absorb-left : (e : A) (_✧_ : A → A → A) → _
Absorb-left {A} e _✧_ = Π[ x ꞉ A ] (e ✧ x ＝ e)

Absorb-right : (e : A) (_✧_ : A → A → A) → _
Absorb-right {A} e _✧_ = Π[ x ꞉ A ] (x ✧ e ＝ e)

-- rigs (absorptive semirings)

record is-rig
  {A : Type ℓ} (0a : A) (_+_ : A → A → A)
               (1a : A) (_*_ : A → A → A): Type ℓ where
  no-eta-equality
  field has-is-semiring : is-semiring 0a _+_ 1a _*_
  open is-semiring has-is-semiring public

  field
    absorb-l : Absorb-left 0a _*_
    absorb-r : Absorb-right 0a _*_

unquoteDecl is-rig-iso = declare-record-iso is-rig-iso (quote is-rig)

instance
  is-rig-is-prop : is-prop (is-rig e _✦_ u _✧_)
  is-rig-is-prop = is-prop-η λ x → let open is-rig x in is-prop-β
    (is-of-hlevel-≃ 1 (iso→equiv is-rig-iso) hlevel!) x

Rig-on : Type ℓ → Type ℓ
Rig-on X =
  Σ[ (0a , _+_ , 1a , _*_) ꞉ X × (X → X → X) × X × (X → X → X) ] (is-rig 0a _+_ 1a _*_)

private
  rig-desc : Desc ℓ ℓ Raw-∞-semiring-on ℓ
  rig-desc .Desc.descriptor = auto-str-term!
  rig-desc .Desc.axioms _ = is-rig $⁴_
  rig-desc .Desc.axioms-prop _ _ = is-rig-is-prop

rig-str : Structure ℓ _
rig-str = desc→structure rig-desc

@0 rig-str-is-univalent : is-univalent (rig-str {ℓ = ℓ})
rig-str-is-univalent = desc→is-univalent rig-desc

Rig : (ℓ : Level) → Type (ℓsuc ℓ)
Rig ℓ = Σ[ X ꞉ Type ℓ ] Rig-on X

instance
  Underlying-Rig : Underlying (Rig ℓ)
  Underlying-Rig {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-Rig .⌞_⌟ = fst
