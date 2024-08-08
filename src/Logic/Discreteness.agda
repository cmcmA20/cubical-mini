{-# OPTIONS --safe #-}
module Logic.Discreteness where

open import Meta.Prelude

open import Logic.Decidability
open import Logic.DoubleNegation

open import Data.Bool.Base as Bool
open import Data.Bool.Path
open import Data.Dec.Base as Dec
open import Data.Dec.Path
open import Data.Empty.Base as ⊥
open import Data.Reflects.Base
open import Data.Unit.Base

open import Functions.Embedding

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

is-¬¬-separated : Type ℓ → Type ℓ
is-¬¬-separated A = ¬¬_ separated A

¬¬-separated-identity-system
  : is-¬¬-separated A
  → is-identity-system (mapⁿ 2 ¬¬_ _＝_) (λ _ k → k refl)
¬¬-separated-identity-system A-sep =
  set-identity-system! $ A-sep _ _

is-¬¬-separated→is-set : is-¬¬-separated A → is-set A
is-¬¬-separated→is-set As =
  identity-system→is-of-hlevel! 1 (¬¬-separated-identity-system As)

opaque
  is-¬¬-separated-is-prop : is-prop (is-¬¬-separated A)
  is-¬¬-separated-is-prop As As′ =
    fun-ext λ x i y p j → (is-¬¬-separated→is-set As) x y (As _ _ p) (As′ _ _ p) i j


is-discrete : Type ℓ → Type ℓ
is-discrete A = {x y : A} → Dec (x ＝ y)

_≟_ : {ℓ : Level} {A : Type ℓ} ⦃ di : is-discrete A ⦄
    → (x y : A) → Dec (x ＝ y)
_≟_ ⦃ di ⦄ x y = di

is-discrete→is-¬¬-separated : is-discrete A → is-¬¬-separated A
is-discrete→is-¬¬-separated di _ _ = dec→essentially-classical di

-- Hedberg
is-discrete→is-set : is-discrete A → is-set A
is-discrete→is-set = is-¬¬-separated→is-set ∘ is-discrete→is-¬¬-separated

opaque
  is-discrete-is-prop : is-prop (is-discrete A)
  is-discrete-is-prop d₁ d₂ i =
    dec-is-of-hlevel 1 (is-discrete→is-set d₁ _ _) d₁ d₂ i

instance
  H-Level-is-discrete : ∀ {n} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (is-discrete A)
  H-Level-is-discrete ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance is-discrete-is-prop
  {-# OVERLAPPING H-Level-is-discrete #-}

  H-Level-hedberg : ∀ {n} → ⦃ di : is-discrete A ⦄ → ⦃ n ≥ʰ 2 ⦄ → H-Level n A
  H-Level-hedberg ⦃ di ⦄ ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 (is-discrete→is-set auto)
  {-# INCOHERENT H-Level-hedberg #-}

↣→is-discrete : (A ↣ B) → is-discrete B → is-discrete A
↣→is-discrete (f , f-inj) B-dis = Dec.dmap f-inj (_∘ ap f) B-dis

↪→is-discrete : (A ↪ B) → is-discrete B → is-discrete A
↪→is-discrete = ↪→↣ ∙ ↣→is-discrete

≃→is-discrete : (B ≃ A) → is-discrete A → is-discrete B
≃→is-discrete = ≃→↪ ∙ ↪→is-discrete

instance
  Σ-is-discrete
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : A → Type ℓ′}
    → ⦃ A-d : is-discrete A ⦄ → ⦃ B-d : ∀[ is-discrete ∘ B ] ⦄
    → is-discrete Σ[ B ]
  Σ-is-discrete {B} ⦃ A-d ⦄ ⦃ B-d ⦄ {a₁ , b₁} {a₂ , b₂} with A-d
  ... | no  a₁≠a₂ = no $ a₁≠a₂ ∘ ap fst
  ... | yes a₁=a₂ with B-d
  ... | no  b₁≠b₂ = no λ r → b₁≠b₂ $ from-pathᴾ $
    subst (λ X → ＜ b₁ ／ (λ i → B (X i)) ＼ b₂ ＞)
          (is-discrete→is-set A-d a₁ a₂ (ap fst r) a₁=a₂)
          (ap snd r)
  ... | yes b₁=b₂ = yes $ Σ-path a₁=a₂ b₁=b₂
  {-# OVERLAPS Σ-is-discrete #-}

  ×-is-discrete : ⦃ A-d : is-discrete A ⦄ → ⦃ B-d : is-discrete B ⦄
                → is-discrete (A × B)
  ×-is-discrete ⦃ A-d ⦄ ⦃ B-d ⦄ with A-d
  ... | no  a₁≠a₂ = no $ a₁≠a₂ ∘ ap fst
  ... | yes a₁=a₂ with B-d
  ... | no  b₁≠b₂ = no $ b₁≠b₂ ∘ ap snd
  ... | yes b₁=b₂ = yes $ a₁=a₂ ,ₚ b₁=b₂
  {-# OVERLAPPING ×-is-discrete #-}

  lift-is-discrete : ⦃ di : is-discrete A ⦄ → is-discrete (Lift ℓ A)
  lift-is-discrete ⦃ di ⦄ {lift x} {lift y} =
    Dec.dmap (ap lift) (_∘ ap lower) di
  {-# OVERLAPPING lift-is-discrete #-}

discrete-eq : {A : Type ℓ} ⦃ A-dis : is-discrete A ⦄
                  → {x y : A} {C : Dec (x ＝ y) → Type ℓ′}
                  → (e : x ＝ y)
                  → C (yes e)
                  → C (x ≟ y)
discrete-eq ⦃ A-dis ⦄ {x} {y} {C} e cy =
  Dec.elim {C = C}
    (λ p → subst (C ∘ yes) (path-is-of-hlevel 1 (is-discrete→is-set A-dis) x y e p) cy)
    (λ ¬e → absurd (¬e e))
    (x ≟ y)

discrete-ne : {A : Type ℓ} ⦃ A-dis : is-discrete A ⦄
            → {x y : A} {C : Dec (x ＝ y) → Type ℓ′}
            → (ne : x ≠ y)
            → C (no ne)
            → C (x ≟ y)
discrete-ne {x} {y} {C} ne cn =
  Dec.elim {C = C}
    (λ e → absurd (ne e))
    (λ ¬e → subst (C ∘ no) (hlevel 1 ne ¬e) cn)
    (x ≟ y)

-- Automation

discrete-reflects! : ⦃ A-dis : is-discrete A ⦄
                   → {x y : A}
                   → Reflects (x ＝ y) ⌊ x ≟ y ⌋
discrete-reflects! {x} {y} =
  Dec.elim {C = λ d → Reflects (x ＝ y) ⌊ d ⌋} ofʸ ofⁿ (x ≟ y)

Refl-is-true : ⦃ A-dis : is-discrete A ⦄ → Refl {A = A} (λ x y → is-true ⌊ x ≟ y ⌋)
Refl-is-true .refl {x} = reflects-true (discrete-reflects! {x = x}) reflₚ

Refl-is-trueₚ : ⦃ A-dis : is-discrete A ⦄ → Refl {A = A} (λ x y → is-trueₚ ⌊ x ≟ y ⌋)
Refl-is-trueₚ .refl {x} = Dec.elim {C = λ d → is-trueₚ (d .does)} (λ _ → refl) (λ ¬refl → ⊥.rec (¬refl refl)) (x ≟ x)

discrete-identity-system
  : {A : Type ℓ} ⦃ A-dis : is-discrete A ⦄
  → is-identity-system {A = A} (λ x y → is-true ⌊ x ≟ y ⌋) (λ _ → Refl-is-true ⦃ A-dis ⦄ .refl)
discrete-identity-system .to-path = true-reflects discrete-reflects!
discrete-identity-system .to-path-over _ = prop!

discrete-identity-systemₚ
  : {A : Type ℓ} ⦃ A-dis : is-discrete A ⦄
  → is-identity-system {A = A} (λ x y → is-trueₚ ⌊ x ≟ y ⌋) (λ _ → Refl-is-trueₚ ⦃ A-dis ⦄ .refl)
discrete-identity-systemₚ = transfer-identity-system discrete-identity-system
  (λ _ _ → is-true≃is-trueₚ) (λ _ → prop!)

↣→is-discrete! : (A ↣ B) → ⦃ di : is-discrete B ⦄ → is-discrete A
↣→is-discrete! f = ↣→is-discrete f auto

↪→is-discrete! : (A ↪ B) → ⦃ di : is-discrete B ⦄ → is-discrete A
↪→is-discrete! f = ↪→is-discrete f auto

≃→is-discrete! : (A ≃ B) → ⦃ di : is-discrete B ⦄ → is-discrete A
≃→is-discrete! f = ≃→is-discrete f auto


-- Usage
private
  module _ {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} ⦃ A-dis : is-discrete A ⦄ {B : A → Type ℓᵇ} ⦃ B-dis : ∀[ mapⁿ 1 is-discrete B ] ⦄ where
    _ : is-discrete (A × A × A × A)
    _ = auto

    _ : is-discrete (Σ[ B ] × Lift ℓᵇ A)
    _ = auto

    _ : is-set (Σ[ B ] ≃ Lift ℓᵇ A)
    _ = hlevel 2

    _ : is-groupoid (Lift ℓᵇ A ≃ Σ[ B ])
    _ = hlevel 3

    _ : {a₁ a₂ : A} (p : is-trueᵈ (a₁ ≟ a₂)) → a₁ ＝ a₂
    _ = true-reflects discrete-reflects!

    _ : {a₁ a₂ : A} (p : is-trueₚ ⌊ a₁ ≟ a₂ ⌋) → a₁ ＝ a₂
    _ = λ p → true-reflects discrete-reflects! (is-true≃is-trueₚ ⁻¹ $ p)
