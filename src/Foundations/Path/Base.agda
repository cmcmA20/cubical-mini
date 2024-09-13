{-# OPTIONS --safe #-}
module Foundations.Path.Base where

open import Foundations.Base

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴
  w x y z : A

opaque
  unfolding _∙ₚ_
  sym-∙ : (p : x ＝ y) (q : y ＝ z) → symₚ (p ∙ₚ q) ＝ symₚ q ∙ₚ symₚ p
  sym-∙ p q _ j = (p ∙ₚ q) (~ j)

instance
  Whisker-i-Pathᴾ
    : {ℓx ℓa ℓb ℓh ℓf ℓhf : Level}
      {X : 𝒰 ℓx} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
      {H : X → A → 𝒰 ℓh} {F : A → B → 𝒰 ℓf}
      {H∙F : X → B → 𝒰 ℓhf} ⦃ _ : Comp H F H∙F ⦄
      {x : X} {a : A} {b b′ : B}
    → Whisker-i H F F _＝_ H∙F H∙F
        x a b b′
        (λ p → Pathᴾ λ i → F   a (p i))
        (λ p → Pathᴾ λ i → H∙F x (p i))
  Whisker-i-Pathᴾ ._◁_ h s i = h ∙ s i
  {-# INCOHERENT Whisker-i-Pathᴾ #-}

  Whisker-o-Pathᴾ
    : {ℓx ℓa ℓb ℓk ℓf ℓfk : Level}
      {X : 𝒰 ℓx} {A : 𝒰 ℓa} {B : 𝒰 ℓb}
      {K : B → X → 𝒰 ℓk} {F : A → B → 𝒰 ℓf}
      {F∙K : A → X → 𝒰 ℓfk} ⦃ _ : Comp F K F∙K ⦄
      {a a′ : A} {b : B} {x : X}
    → Whisker-o F F _＝_ K F∙K F∙K
        a a′ b x
        (λ p → Pathᴾ λ i → F   (p i) b)
        (λ p → Pathᴾ λ i → F∙K (p i) x)
  Whisker-o-Pathᴾ ._▷_ s k i = s i ∙ k
  {-# INCOHERENT Whisker-o-Pathᴾ #-}

opaque
  unfolding _∙ₚ_
  infixr 30 _∙ᴾ_
  _∙ᴾ_ : {A : Type ℓ} {B : A → Type ℓ′} {x y z : A} {x′ : B x} {y′ : B y} {z′ : B z} {p : x ＝ y} {q : y ＝ z}
       → ＜ x′ ／ (λ i → B (p i)) ＼ y′ ＞
       → ＜ y′ ／ (λ i → B (q i)) ＼ z′ ＞
       → ＜ x′ ／ (λ i → B ((p ∙ q) i)) ＼ z′ ＞
  _∙ᴾ_ {B} {y} {x′} {y′} {p} {q} p′ q′ i =
    comp (λ j → B (∙-filler p q j i)) (∂ i) λ where
      j (i = i0) → p′ (~ j)
      j (i = i1) → q′ j
      j (j = i0) → y′

module _
  {a₀₀ a₁₀ a₀₁ a₁₁ : A}
  {p : a₀₀ ＝ a₀₁} {q : a₀₀ ＝ a₁₀} {r : a₁₀ ＝ a₁₁} {s : a₀₁ ＝ a₁₁} where opaque

  -- Vertical composition of squares
  infixr 30 _∙ᵥ_
  _∙ᵥ_ : {a₀₂ a₁₂ : A} {t : a₀₁ ＝ a₀₂} {u : a₁₁ ＝ a₁₂} {v : a₀₂ ＝ a₁₂}
       → Square p q r s → Square t s u v
       → Square (p ∙ t) q (r ∙ u) v
  _∙ᵥ_ {t} {u} α β j i = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → ∙-filler p t k j
    k (i = i1) → ∙-filler r u k j
    k (j = i0) → α (~ k) i
    k (j = i1) → β k i
    k (k = i0) → s i

  -- Horizontal composition of squares
  infixr 30 _∙ₕ_
  _∙ₕ_ : {a₂₀ a₂₁ : A} {t : a₁₀ ＝ a₂₀} {u : a₁₁ ＝ a₂₁} {v : a₂₀ ＝ a₂₁}
       → Square p q r s → Square r t v u
       → Square p (q ∙ t) v (s ∙ u)
  _∙ₕ_ = apᴾ² λ _ → _∙_

-- opaque
--   unfolding _∙_ _∙ᵥ_ _∙ₕ_
--   square-eckmann-hilton
--     : {a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : A}
--       {p : a₀₀ ＝ a₀₁} {q : a₀₀ ＝ a₁₀} {r : a₁₀ ＝ a₁₁} {s : a₀₁ ＝ a₁₁} {α : Square p q r s}
--       {t : a₁₀ ＝ a₂₀} {u : a₂₀ ＝ a₂₁} {v : a₁₁ ＝ a₂₁} {β : Square r t u v}
--       {w : a₀₁ ＝ a₀₂} {y : a₁₁ ＝ a₁₂} {x : a₀₂ ＝ a₁₂} {γ : Square w s y x}
--       {z : a₂₁ ＝ a₂₂} {o : a₁₂ ＝ a₂₂} {δ : Square y v z o}
--     → (α ∙ₕ β) ∙ᵥ (γ ∙ₕ δ) ＝ (α ∙ᵥ γ) ∙ₕ (β ∙ᵥ δ)
--   square-eckmann-hilton {p} {q} {r} {s} {α} {t} {β} {γ} {δ} i j k = hfill (∂ j ∨ ∂ k) (~ i) λ where
--     l (j = i0) → {!!}
--     l (j = i1) → {!!}
--     l (k = i0) → {!!}
--     l (k = i1) → {!!}
--     l (l = i0) → {!!}
