{-# OPTIONS --safe --no-exact-split #-}
module Order.Ordinal where

open import Cat.Prelude
open import Foundations.HLevel.Closure

open import Order.Base
open import Data.Acc.Base
open import Data.Truncation.Propositional

private variable n : HLevel

record WESet o ℓ : 𝒰 (ℓsuc (o ⊔ ℓ)) where
  no-eta-equality
  infix 4.5 _<_
  field
    Ob  : 𝒰 o
    _<_ : Ob → Ob → 𝒰 ℓ
    <-thin : ∀ {x y} → is-prop (x < y)
    <-wf   : is-wf _<_
    <-lext : ∀ {x y} → (∀ z → (z < x) ≃ (z < y)) → x ＝ y

  opaque
    instance
      H-Level-<-prop : ∀ {x y} → H-Level (suc n) (x < y)
      H-Level-<-prop = hlevel-prop-instance <-thin

    ob-is-set : is-set Ob
    ob-is-set = identity-system→is-of-hlevel! 1
      {R = λ x y → ∀ z → (z < x) ≃ (z < y)}
      {r = λ x z → refl}
      (set-identity-system! <-lext)

unquoteDecl weset-iso = declare-record-iso weset-iso (quote WESet)

-- TODO refactor
Ordinal : ∀ ℓ → 𝒰 (ℓsuc ℓ)
Ordinal ℓ = Σ[ W ꞉ WESet ℓ ℓ ] (∀ {x y z} → WESet._<_ W x y → WESet._<_ W y z → WESet._<_ W x z)

private variable o o′ o″ o‴ ℓ ℓ′ ℓ″ ℓ‴ : Level

module _ (P : WESet o ℓ) (Q : WESet o′ ℓ′) where
  private
    module P = WESet P
    module Q = WESet Q

  record Simulation∃ : 𝒰 (o ⊔ o′ ⊔ ℓ ⊔ ℓ′) where
    no-eta-equality
    constructor mk-simulation∃
    field
      sim     : P.Ob → Q.Ob
      is-mono : ∀{x y} → x P.< y → sim x Q.< sim y
      ∃-lift  : ∀{x y} → y Q.< sim x → ∃[ x′ ꞉ P.Ob ] (x′ P.< x) × (sim x′ ＝ y)
  {-# INLINE mk-simulation∃ #-}

open Simulation∃ public

simulation∃→injective : {P : WESet o ℓ} {Q : WESet o′ ℓ′}
                        (f : Simulation∃ P Q)
                      → Injective (sim f)
simulation∃→injective {P} {Q} f {x} {y} =
  to-induction P.<-wf (λ a → ∀ b → sim f a ＝ sim f b → a ＝ b)
    (λ a ih b e → P.<-lext λ z →
       prop-extₑ!
         (λ z<a → ∥-∥₁.elim (λ _ → P.<-thin)
                       (λ where (q , q<b , fq=fz) →
                                  subst (P._< b) (ih z z<a q (fq=fz ⁻¹) ⁻¹) q<b)
                       (Simulation∃.∃-lift f
                          (subst (sim f z Q.<_) e $ Simulation∃.is-mono f z<a)))
         (λ z<b → ∥-∥₁.elim (λ _ → P.<-thin)
                       (λ where (q , q<a , fq=fz) →
                                  subst (P._< a) (ih q q<a z fq=fz) q<a)
                       (Simulation∃.∃-lift f
                          (subst (sim f z Q.<_) (e ⁻¹) $ Simulation∃.is-mono f z<b))))
    x y
  where
    module P = WESet P
    module Q = WESet Q

simulation∃→is-embedding : {P : WESet o ℓ} {Q : WESet o′ ℓ′}
                           (f : Simulation∃ P Q)
                         → is-embedding (sim f)
simulation∃→is-embedding {P} {Q} =
  set-injective→is-embedding (WESet.ob-is-set Q) ∘ₜ simulation∃→injective

-- TODO expand
