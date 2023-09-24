{-# OPTIONS --safe --overlapping-instances --instance-search-depth=1 #-}
module Algebra.Semigroup where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Record
open import Meta.Search.HLevel
open import Meta.SIP
open import Meta.Underlying

open import Algebra.Magma public

private variable
  ℓ : Level
  A : Type ℓ
  _✦_ : A → A → A
  x y z w : A

Associative : (_⋆_ : A → A → A) → Type _
Associative {A} _⋆_ = (x y z : A) → x ⋆ (y ⋆ z) ＝ (x ⋆ y) ⋆ z

Raw-∞-semigroup-on : Type ℓ → Type ℓ
Raw-∞-semigroup-on = ∞-Magma-on

Wild-∞-semigroup-on : Type ℓ → Type ℓ
Wild-∞-semigroup-on X = Σ[ _⋆_ ꞉ (X → X → X) ] (Associative _⋆_)


-- 2-semigroups

record 2-semigroup {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    has-is-2-magma : is-2-magma _⋆_
    assoc          : Associative _⋆_
    assoc-coh      :  assoc x y (z ⋆ w) ∙ assoc (x ⋆ y) z w
                   ＝ ap (x ⋆_) (assoc y z w)
                    ∙ assoc x (y ⋆ z) w
                    ∙ ap (_⋆ w) (assoc x y z)

  open is-n-magma has-is-2-magma public

private unquoteDecl 2-semigroup-iso = declare-record-iso 2-semigroup-iso (quote 2-semigroup)

instance
  2-semigroup-is-set : is-set (2-semigroup _✦_)
  2-semigroup-is-set = is-set-η λ x → let open 2-semigroup x in is-set-β
    (is-of-hlevel-≃ 2 (iso→equiv 2-semigroup-iso) hlevel!) x

2-semigroup-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) (2-semigroup _✦_)
2-semigroup-is-of-hlevel n = is-of-hlevel-+-left 2 n 2-semigroup-is-set

instance
  decomp-hlevel-2-semigroup : goal-decomposition (quote is-of-hlevel) (2-semigroup _✦_)
  decomp-hlevel-2-semigroup = decomp (quote 2-semigroup-is-of-hlevel) (`level-minus 2 ∷ [])


2-Semigroup-on : Type ℓ → Type ℓ
2-Semigroup-on X = Σ[ _⋆_ ꞉ (X → X → X) ] (2-semigroup _⋆_)

2-Semigroup : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
2-Semigroup ℓ = Σ[ X ꞉ Type ℓ ] 2-Semigroup-on X

instance
  Underlying-2-Semigroup : Underlying (2-Semigroup ℓ)
  Underlying-2-Semigroup {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-2-Semigroup .⌞_⌟ = fst


-- semigroups

record is-semigroup {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    has-is-magma : is-magma _⋆_
    assoc        : (x y z : A) → x ⋆ (y ⋆ z) ＝ (x ⋆ y) ⋆ z

  open is-n-magma has-is-magma public

unquoteDecl is-semigroup-iso = declare-record-iso is-semigroup-iso (quote is-semigroup)

instance
  is-semigroup-is-prop : is-prop (is-semigroup _✦_)
  is-semigroup-is-prop = is-prop-η λ x → let open is-semigroup x in is-prop-β
    (is-of-hlevel-≃ 1 (iso→equiv is-semigroup-iso) hlevel!) x

is-semigroup-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) (is-semigroup _✦_)
is-semigroup-is-of-hlevel _ = is-prop→is-of-hlevel-suc is-semigroup-is-prop

is-set→2-semigroup-is-prop : (A-set : is-set A) → is-prop (2-semigroup {A = A} _✦_)
is-set→2-semigroup-is-prop A-set = is-of-hlevel-≃ 1 (iso→equiv 2-semigroup-iso) hlevel! where instance _ = A-set

carrier-is-set→2-semigroup≃is-semigroup : (A-set : is-set A) → 2-semigroup {A = A} _✦_ ≃ is-semigroup _✦_
carrier-is-set→2-semigroup≃is-semigroup {_✦_} A-set = prop-extₑ (is-set→2-semigroup-is-prop A-set) hlevel! to from where
  instance _ = A-set
  to : 2-semigroup _✦_ → is-semigroup _✦_
  to 2-sg .is-semigroup.has-is-magma .is-n-magma.has-is-of-hlevel = A-set
  to 2-sg .is-semigroup.assoc = 2-semigroup.assoc 2-sg

  from : is-semigroup _✦_ → 2-semigroup _✦_
  from sg .2-semigroup.has-is-2-magma .is-n-magma.has-is-of-hlevel = is-of-hlevel-suc 2 A-set
  from sg .2-semigroup.assoc = is-semigroup.assoc sg
  from sg .2-semigroup.assoc-coh = prop!

instance
  decomp-hlevel-is-semigroup : goal-decomposition (quote is-of-hlevel) (is-semigroup _✦_)
  decomp-hlevel-is-semigroup = decomp (quote is-semigroup-is-of-hlevel) (`level-minus 1 ∷ [])


private
  is-semigroup-desc : Desc ℓ ℓ Raw-∞-semigroup-on ℓ
  is-semigroup-desc .Desc.descriptor = auto-str-term!
  is-semigroup-desc .Desc.axioms _ = is-semigroup
  is-semigroup-desc .Desc.axioms-prop _ _ = is-semigroup-is-prop

semigroup-str : Structure ℓ _
semigroup-str = desc→structure is-semigroup-desc

@0 semigroup-str-is-univalent : is-univalent (semigroup-str {ℓ = ℓ})
semigroup-str-is-univalent = desc→is-univalent is-semigroup-desc


Semigroup : (ℓ : Level) → 𝒰 (ℓsuc ℓ)
Semigroup _ = Type-with semigroup-str

instance
  Underlying-Semigroup : Underlying (Semigroup ℓ)
  Underlying-Semigroup {ℓ} .Underlying.ℓ-underlying = ℓ
  Underlying-Semigroup .⌞_⌟ = fst


-- same as magma
module _ {A* B* : Semigroup ℓ} {e : ⌞ A* ⌟ ≃ ⌞ B* ⌟} where private
  _⋆_ = A* .snd .fst
  _☆_ = B* .snd .fst
  module e = Equiv e

  _ :  semigroup-str .is-hom A* B* e
    ＝ Π[ x ꞉ ⌞ A* ⌟ ] Π[ y ꞉ ⌞ A* ⌟ ] (e.to (x ⋆ y) ＝ e.to x ☆ e.to y)
  _ = refl
