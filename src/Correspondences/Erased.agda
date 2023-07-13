{-# OPTIONS --safe #-}
module Correspondences.Erased where

open import Foundations.Base
open import Foundations.HLevel
open import Foundations.Univalence

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

∥-∥ᴱ-equiv : ∥ x ＝ y ∥ᴱ ≃ (∣ x ∣ᴱ ＝ ∣ y ∣ᴱ)
∥-∥ᴱ-equiv .fst = ∣-∣ᴱ-cong
∥-∥ᴱ-equiv .snd .equiv-proof = strict-contr-fibres ∣-∣ᴱ-uncong

substᴱ : (B : @0 A → Type ℓ′) (@0 p : x ＝ y) → B x → B y
substᴱ B p = transport (λ i → B (p i))
-- substᴱ B p = subst (λ z → B (z .erased)) ([]ᴱ-cong [ p ]ᴱ)


-- FIXME doesn't work as intended
--       do we need modality polymorphism?
instance
  Map-∥-∥ᴱ : Map (eff λ T → ∥ T ∥ᴱ)
  Map-∥-∥ᴱ ._<$>_ f ∣ a ∣ᴱ = ∣ f a ∣ᴱ

  Idiom-∥-∥ᴱ : Idiom (eff λ T → ∥ T ∥ᴱ)
  Idiom-∥-∥ᴱ .pure a = ∣ a ∣ᴱ
  Idiom-∥-∥ᴱ ._<*>_ ∣ f ∣ᴱ ∣ a ∣ᴱ = ∣ f a ∣ᴱ

  Bind-∥-∥ᴱ : Bind (eff λ T → ∥ T ∥ᴱ)
  Bind-∥-∥ᴱ ._>>=_ ∣ a ∣ᴱ mf = ∣ mf a .erased ∣ᴱ

opaque
  Recomputable : Type ℓ → Type ℓ
  Recomputable A = ∥ A ∥ᴱ → A

opaque
  unfolding is-of-hlevel
  ∥-∥ᴱ-is-contr : @0 is-contr A → is-contr ∥ A ∥ᴱ
  ∥-∥ᴱ-is-contr (centre , paths) = ∣ centre ∣ᴱ , λ { ∣ x ∣ᴱ → ∣-∣ᴱ-cong ∣ paths x ∣ᴱ }

  ∥-∥ᴱ-is-prop : @0 is-prop A → is-prop ∥ A ∥ᴱ
  ∥-∥ᴱ-is-prop pr ∣ x ∣ᴱ ∣ y ∣ᴱ = ∣-∣ᴱ-cong ∣ pr x y ∣ᴱ

  ∥-∥ᴱ-is-set : @0 is-set A → is-set ∥ A ∥ᴱ
  ∥-∥ᴱ-is-set se ∣ x ∣ᴱ ∣ y ∣ᴱ _ _ = ap ∣-∣ᴱ-cong $ ∣-∣ᴱ-cong ∣ se x y _ _ ∣ᴱ

  @0 ∥-∥ᴱ-is-of-hlevel : (n : HLevel) → @0 is-of-hlevel n A → is-of-hlevel n ∥ A ∥ᴱ
  ∥-∥ᴱ-is-of-hlevel 0 = ∥-∥ᴱ-is-contr
  ∥-∥ᴱ-is-of-hlevel 1 = ∥-∥ᴱ-is-prop
  ∥-∥ᴱ-is-of-hlevel (suc (suc n)) hl ∣ x ∣ᴱ ∣ y ∣ᴱ =
    subst (is-of-hlevel (suc n)) (ua ∥-∥ᴱ-equiv) $ ∥-∥ᴱ-is-of-hlevel (suc n) (hl x y)
