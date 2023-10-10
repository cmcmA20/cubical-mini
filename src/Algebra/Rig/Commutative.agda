{-# OPTIONS --safe --overlapping-instances --instance-search-depth=1 #-}
module Algebra.Rig.Commutative where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel
open import Meta.SIP
open import Meta.Underlying

open import Algebra.Rig public

private variable
  ℓ     : Level
  A     : Type ℓ
  e x y z u : A
  _✦_ _✧_ : A → A → A

-- commutative rigs

record is-comm-rig
  {A : Type ℓ} (0a : A) (_+_ : A → A → A)
               (1a : A) (_*_ : A → A → A): Type ℓ where
  no-eta-equality
  field has-is-rig : is-rig 0a _+_ 1a _*_
  open is-rig has-is-rig public

  field *-comm : Commutative _*_

unquoteDecl is-comm-rig-iso = declare-record-iso is-comm-rig-iso (quote is-comm-rig)

instance
  is-comm-rig-is-prop : is-prop (is-comm-rig e _✦_ u _✧_)
  is-comm-rig-is-prop = is-prop-η λ x → let open is-comm-rig x in is-prop-β
    (is-of-hlevel-≃ 1 (iso→equiv is-comm-rig-iso) hlevel!) x

Comm-rig-on : Type ℓ → Type ℓ
Comm-rig-on X =
  Σ[ (0a , _+_ , 1a , _*_) ꞉ X × (X → X → X) × X × (X → X → X) ] (is-comm-rig 0a _+_ 1a _*_)

private
  comm-rig-desc : Desc ℓ ℓ Raw-∞-semiring-on ℓ
  comm-rig-desc .Desc.descriptor = auto-str-term!
  comm-rig-desc .Desc.axioms _ = is-comm-rig $⁴_
  comm-rig-desc .Desc.axioms-prop _ _ = is-comm-rig-is-prop

comm-rig-str : Structure ℓ _
comm-rig-str = desc→structure comm-rig-desc

@0 comm-rig-str-is-univalent : is-univalent (comm-rig-str {ℓ = ℓ})
comm-rig-str-is-univalent = desc→is-univalent comm-rig-desc

Comm-rig : (ℓ : Level) → Type (ℓsuc ℓ)
Comm-rig ℓ = Σ[ X ꞉ Type ℓ ] Comm-rig-on X

instance
  Underlying-Comm-rig : Underlying (Comm-rig ℓ)
  Underlying-Comm-rig {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-Comm-rig .⌞_⌟ = fst
