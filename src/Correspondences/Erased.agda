{-# OPTIONS --safe #-}
module Correspondences.Erased where

open import Foundations.Base

open import Meta.Bind

record ∥_∥ᴱ {ℓ} (@0 A : Type ℓ) : Type ℓ where
  constructor ∣_∣ᴱ
  field @0 erased : A
open ∥_∥ᴱ public

private variable
  ℓ ℓ′ : Level
  @0 A : Type ℓ
  @0 B : Type ℓ′
  @0 x y : A

instance
  ∥-∥ᴱ-inst : {A : Type ℓ} → ⦃ A ⦄ → ∥ A ∥ᴱ
  ∥-∥ᴱ-inst ⦃ (a) ⦄ .erased = a

∣-∣ᴱ-cong : ∥ x ＝ y ∥ᴱ → ∣ x ∣ᴱ ＝ ∣ y ∣ᴱ
∣-∣ᴱ-cong ∣ p ∣ᴱ = λ i → ∣ p i ∣ᴱ

∣-∣ᴱ-uncong : ∣ x ∣ᴱ ＝ ∣ y ∣ᴱ → ∥ x ＝ y ∥ᴱ
∣-∣ᴱ-uncong p .erased = ap erased p

substᴱ : (B : @0 A → Type ℓ′) (@0 p : x ＝ y) → B x → B y
substᴱ B p = transport (λ i → B (p i))
-- substᴱ B p = subst (λ z → B (z .erased)) ([]ᴱ-cong [ p ]ᴱ)

instance
  Map-∥-∥ᴱ : Map (eff λ T → ∥ T ∥ᴱ)
  Map-∥-∥ᴱ ._<$>_ f ∣ a ∣ᴱ = ∣ f a ∣ᴱ

  Idiom-∥-∥ᴱ : Idiom (eff λ T → ∥ T ∥ᴱ)
  Idiom-∥-∥ᴱ .pure a = ∣ a ∣ᴱ
  Idiom-∥-∥ᴱ ._<*>_ ∣ f ∣ᴱ ∣ a ∣ᴱ = ∣ f a ∣ᴱ

  Bind-∥-∥ᴱ : Bind (eff λ T → ∥ T ∥ᴱ)
  Bind-∥-∥ᴱ ._>>=_ ∣ a ∣ᴱ mf = ∣ mf a .erased ∣ᴱ
