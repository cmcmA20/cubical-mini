{-# OPTIONS --safe #-}
module Logic.Discreteness where

open import Meta.Prelude

open import Logic.Decidability
open import Logic.DoubleNegation

open import Data.Bool.Base as Bool
open import Data.Dec.Base as Dec
open import Data.Dec.Base
  using ( is-discrete ; reflects-path→is-discrete! )
  public
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


_≟_ : ⦃ di : is-discrete A ⦄ (x y : A) → Dec (x ＝ y)
_≟_ ⦃ di ⦄ x y = di

_=?_ : ⦃ di : is-discrete A ⦄ (x y : A) → Bool
_=?_ x y = ⌊ x ≟ y ⌋

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

↣→is-discrete : (B ↣ A) → is-discrete A → is-discrete B
↣→is-discrete (f , f-inj) B-dis = Dec.dmap f-inj (_∘ ap f) B-dis

↪→is-discrete : (B ↪ A) → is-discrete A → is-discrete B
↪→is-discrete = ↪→↣ ∙ ↣→is-discrete

≃→is-discrete : (B ≃ A) → is-discrete A → is-discrete B
≃→is-discrete = ≃→↪ ∙ ↪→is-discrete

≅→is-discrete : (B ≅ A) → is-discrete A → is-discrete B
≅→is-discrete = ≅→≃ ∙ ≃→is-discrete

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


-- Automation

instance
  Reflects-Discrete : ⦃ di : is-discrete A ⦄ {x y : A} → Reflects (x ＝ y) ⌊ x ≟ y ⌋
  Reflects-Discrete {x} {y} = Reflects-does (x ≟ y)
  {-# INCOHERENT Reflects-Discrete #-}

given-yes_return_then_
  : {A : Type ℓ} ⦃ d : Dec A ⦄ ⦃ A-pr : H-Level 1 A ⦄
    (a : A) (C : Dec A → Type ℓ′)
  → C (yes a) → C d
given-yes_return_then_ {A} a C cy = caseᵈ A return C of λ where
  (yes a′) → subst C prop! cy
  (no  ¬a) → false! (¬a a)

given-no_return_then_
  : {A : Type ℓ} ⦃ d : Dec A ⦄ ⦃ A-pr : H-Level 1 A ⦄
    (¬a : ¬ A) (C : Dec A → Type ℓ′)
  → C (no ¬a) → C d
given-no_return_then_ {A} ¬a C cy = caseᵈ A return C of λ where
  (yes a)   → false! (¬a a)
  (no  ¬a′) → subst (C ∘ no) prop! cy

↣→is-discrete! : (A ↣ B) → ⦃ di : is-discrete B ⦄ → is-discrete A
↣→is-discrete! f = ↣→is-discrete f auto

↪→is-discrete! : (A ↪ B) → ⦃ di : is-discrete B ⦄ → is-discrete A
↪→is-discrete! f = ↪→is-discrete f auto

≃→is-discrete! : (A ≃ B) → ⦃ di : is-discrete B ⦄ → is-discrete A
≃→is-discrete! f = ≃→is-discrete f auto

≅→is-discrete! : (A ≅ B) → ⦃ di : is-discrete B ⦄ → is-discrete A
≅→is-discrete! f = ≅→is-discrete f auto

-- -- Usage
-- private
--   module _ {ℓᵃ ℓᵇ : Level} {A : Type ℓᵃ} ⦃ A-dis : is-discrete A ⦄ {B : A → Type ℓᵇ} ⦃ B-dis : ∀[ mapⁿ 1 is-discrete B ] ⦄ where
--     _ : is-discrete (A × A × A × A)
--     _ = auto

--     _ : is-discrete (Σ[ B ] × Lift ℓᵇ A)
--     _ = auto

--     _ : is-set (Σ[ B ] ≃ Lift ℓᵇ A)
--     _ = hlevel 2

--     _ : is-groupoid (Lift ℓᵇ A ≃ Σ[ B ])
--     _ = hlevel 3

--     _ : {a₁ a₂ : A} (p : Soᵈ (a₁ ≟ a₂)) → a₁ ＝ a₂
--     _ = so→true!

--     _ : {a₁ a₂ : A} (p : is-true ⌊ a₁ ≟ a₂ ⌋) → a₁ ＝ a₂
--     _ = λ p → so→true! (so≃is-true ⁻¹ $ p)
