{-# OPTIONS --safe --overlapping-instances --instance-search-depth=4 #-}
open import Cubical.Algebra.Monoid.Base
module Cubical.Algebra.Monoid.Cayley {ℓᵐ} (ℳ : Monoid ℓᵐ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Erased

open import Cubical.Data.Sigma

open import Cubical.Instances.HLevels

open MonoidStr (str ℳ)
open Iso

private instance
  carrier-set : IsSet ⟨ ℳ ⟩
  carrier-set = is-set

𝓜 : Monoid ℓᵐ
𝓜 = makeMonoid {M = ⟨ ℳ ⟩ → ⟨ ℳ ⟩} (λ x → x) (λ f g → f ∘ g) (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)

open MonoidStr (𝓜 .snd) using () renaming (_·_ to _⋆_; ε to ε′)

inc : ⟨ ℳ ⟩ → ⟨ 𝓜 ⟩
inc m = m ·_

inc-homo : ∀ g h → inc (g · h) ≡ inc g ⋆ inc h
inc-homo _ _ = funExt λ _ → sym (·Assoc _ _ _)

inc-presε : inc ε ≡ ε′
inc-presε = funExt λ _ → ·IdL _

Representable : ⟨ 𝓜 ⟩ → Type ℓᵐ
Representable f = ∀ x g h → x ≡ g · h → f x ≡ (f g) · h

instance
  Representable-prop : {f : ⟨ 𝓜 ⟩} → IsProp (Representable f)
  IsOfHLevel.iohl Representable-prop = isPropΠ2 λ _ _ → isPropΠ2 λ _ _ → is-set .iohl _ _

Repr : Type ℓᵐ
Repr = Σ[ f ∈ ⟨ 𝓜 ⟩ ] Erased (Representable f)

Repr≡ : {f′ g′ : Repr} → f′ .fst ≡ g′ .fst → f′ ≡ g′
Repr≡ {f′ = f , fr} {g′ = g , gr} p = ΣPathP (p , isProp→PathP (λ _ → helper .iohl) fr gr)
  where
  helper : {f : _} → IsProp (Erased (Representable f))
  helper = it

compose : (f′ g′ : Repr) → Repr
compose (f , [ fr ]) (g , [ gr ]) = f ⋆ g , [ (λ x u v p → fr (g x) (g u) v (gr x u v p)) ]

ReprMonoidStr : MonoidStr Repr
MonoidStr.ε        ReprMonoidStr = ε′ , [ (λ _ _ _ p → p) ]
MonoidStr._·_      ReprMonoidStr = compose
MonoidStr.isMonoid ReprMonoidStr = makeIsMonoid (λ _ _ _ → refl) (λ _ → refl) (λ _ → refl)

𝔐 : Monoid ℓᵐ
𝔐 = Repr , ReprMonoidStr

open MonoidStr (𝔐 .snd) using () renaming (_·_ to _✦_; ε to ε″)

inc-rep : (x : ⟨ ℳ ⟩) → Representable (inc x)
inc-rep x y g h p =
    x · y       ≡⟨ cong (x ·_) p ⟩
    x · (g · h) ≡⟨ ·Assoc _ _ _ ⟩
    (x · g) · h ∎

rep-inc : (f′ : Repr) → Σ[ g ∈ ⟨ ℳ ⟩ ] Erased (inc g ≡ f′ .fst)
rep-inc (f , [ fr ]) = f ε , [ (funExt λ _ → sym (fr _ _ _ (sym (·IdL _)))) ]

incᵣ : ⟨ ℳ ⟩ → ⟨ 𝔐 ⟩
incᵣ g = inc g , [ inc-rep g ]

@0 incᵣ-iso : Iso ⟨ ℳ ⟩ ⟨ 𝔐 ⟩
incᵣ-iso .fun = incᵣ
incᵣ-iso .inv = fst ∘ rep-inc
incᵣ-iso .leftInv    = ·IdR
incᵣ-iso .rightInv f = let x , [ p ] = rep-inc f in Repr≡ p

@0 incᵣ-equiv : ⟨ ℳ ⟩ ≃ ⟨ 𝔐 ⟩
incᵣ-equiv = isoToEquiv incᵣ-iso

incᵣ-homo : ∀ g h → incᵣ (g · h) ≡ incᵣ g ✦ incᵣ h
incᵣ-homo g h = Repr≡ $ inc-homo g h

incᵣ-presε : incᵣ ε ≡ ε″
incᵣ-presε = Repr≡ inc-presε

@0 meq : MonoidEquiv ℳ 𝔐
meq = incᵣ-equiv , monoidequiv incᵣ-presε incᵣ-homo

@0 lookAtThis : ℳ ≡ 𝔐
lookAtThis = equivFun (MonoidPath ℳ 𝔐) meq

@0 strictify : {ℓ′ : Level} → (P : Monoid ℓᵐ → Type ℓ′) → P 𝔐 → P ℳ
strictify P = transport (sym (cong P lookAtThis))
