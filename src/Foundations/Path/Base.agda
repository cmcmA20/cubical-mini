{-# OPTIONS --safe #-}
module Foundations.Path.Base where

open import Foundations.Prelude

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  w x y z : A

module _ where private

  -- We could have also defined single composition by taking `refl` on the right
  infixr 30 _∙′_
  _∙′_ : x ＝ y → y ＝ z → x ＝ z
  p ∙′ q = p ∙∙ q ∙∙ refl

  ∙′-filler : (p : x ＝ y) (q : y ＝ z)
            →  y  ̇      q       ̇ z
                   ┌─────────┐ _
                   │    _    │
           sym p   │    _    │   refl
                   │    _    │ _
                   └─────────┘
               x  ̇    p ∙′ q    ̇ z
  ∙′-filler p q = ∙∙-filler p q refl

  -- From this, we can show that these two notions of composition are the same
  ∙＝∙′ : (p : x ＝ y) (q : y ＝ z) → p ∙ q ＝ p ∙′ q
  ∙＝∙′ p q j = ∙∙-unique p q refl (p ∙ q , ∙-filler′ p q) (p ∙′ q , ∙′-filler p q) j .fst

  -- We could define double composition with top side `refl`
  -- Seems strange not to prefer this version
  infixr 30 _∙″_
  _∙″_ : x ＝ y → y ＝ z → x ＝ z
  p ∙″ q = p ∙∙ refl ∙∙ q

  ∙″-filler : (p : x ＝ y) (q : y ＝ z)
            →  y  ̇    refl      ̇ y
                   ┌─────────┐ _
                   │    _    │
           sym p   │    _    │   q
                   │    _    │ _
                   └─────────┘
               x  ̇    p ∙″ q    ̇ z
  ∙″-filler p q = ∙∙-filler p refl q

  ∙-filler″ : (p : x ＝ y) (q : y ＝ z)
            →  y  ̇    refl      ̇ y
                   ┌─────────┐ _
                   │    _    │
           sym p   │    _    │   q
                   │    _    │ _
                   └─────────┘
               x  ̇    p ∙ q     ̇ z
  ∙-filler″ {y} p q j i = hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p (~ j)
    k (i = i1) → q (j ∧ k)
    k (j = i0) → y
    k (k = i0) → p (i ∨ ~ j)

  ∙＝∙″ : (p : x ＝ y) (q : y ＝ z) → p ∙ q ＝ p ∙″ q
  ∙＝∙″ p q j = ∙∙-unique p refl q (p ∙ q , ∙-filler″ p q) (p ∙″ q , ∙″-filler p q) j .fst

invert-sides : (p : x ＝ y) (q : x ＝ z) → Square q p (sym p) (sym q)
invert-sides {x} p q i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → p (k ∧ j)
  k (i = i1) → q (k ∧ ~ j)
  k (j = i0) → q (k ∧ i)
  k (j = i1) → p (k ∧ ~ i)
  k (k = i0) → x

sym-∙ : (p : x ＝ y) (q : y ＝ z)
      → sym (p ∙ q) ＝ sym q ∙ sym p
sym-∙ {z} p q i j = sym-∙-filler j i i1
  where
  sym-∙-filler : I → I → I → _
  sym-∙-filler i j k = hfill (∂ i) k λ where
    l (i = i0) → q (l ∨ j)
    l (i = i1) → p (~ l ∧ j)
    l (l = i0) → invert-sides q (sym p) i j


-- Whiskering a dependent path by a path

-- Double whiskering
infix 8 _◁_▷_
_◁_▷_ : {A : I → Type ℓ} {a₀ a₀′ : A i0} {a₁ a₁′ : A i1}
      →    a₀ ＝ a₀′ → ＜ a₀′ ／ A ＼ a₁ ＞ → a₁ ＝ a₁′
      → ＜ a₀              ／    A    ＼            a₁′ ＞
(p ◁ P ▷ q) i = hcomp (∂ i) λ where
  j (i = i0) → p (~ j)
  j (i = i1) → q j
  j (j = i0) → P i

double-whiskering-filler
  : {A : I → Type ℓ} {a₀ a₀′ : A i0} {a₁ a₁′ : A i1}
  → (p : a₀ ＝ a₀′) (pq : PathP A a₀′ a₁) (q : a₁ ＝ a₁′)
  → ＜ pq ／ (λ i → ＜ p (~ i) ／ A ＼ q i ＞) ＼ p ◁ pq ▷ q ＞
double-whiskering-filler p pq q k i = hfill (∂ i) k λ where
  j (i = i0) → p (~ j)
  j (i = i1) → q j
  j (j = i0) → pq i

infix 24 _◁_
_◁_ : {A : I → Type ℓ} {a₀ a₀′ : A i0} {a₁ : A i1}
    →    a₀ ＝ a₀′ → ＜ a₀′ ／ A ＼    a₁ ＞
    → ＜ a₀              ／    A    ＼ a₁ ＞
(p ◁ q) = p ◁ q ▷ refl

infix 24 _▷_
_▷_ : {A : I → Type ℓ} {a₀ : A i0} {a₁ a₁′ : A i1}
    → ＜ a₀    ／ A ＼ a₁ ＞ → a₁ ＝ a₁′
    → ＜ a₀ ／    A    ＼            a₁′ ＞
p ▷ q  = refl ◁ p ▷ q


-- Horizontal composition of squares (along their second dimension)

-- infixr 30 _∙₂_
-- _∙₂_ :
--   {a₀₀ a₀₁ a₀₂ : A} {a₀₋ : a₀₀ ＝ a₀₁} {b₀₋ : a₀₁ ＝ a₀₂}
--   {a₁₀ a₁₁ a₁₂ : A} {a₁₋ : a₁₀ ＝ a₁₁} {b₁₋ : a₁₁ ＝ a₁₂}
--   {a₋₀ : a₀₀ ＝ a₁₀} {a₋₁ : a₀₁ ＝ a₁₁} {a₋₂ : a₀₂ ＝ a₁₂}
--   (p : Square a₀₋ a₁₋ a₋₀ a₋₁) (q : Square b₀₋ b₁₋ a₋₁ a₋₂)
--   → Square (a₀₋ ∙ b₀₋) (a₁₋ ∙ b₁₋) a₋₀ a₋₂
-- _∙₂_ = congP₂ (λ _ → _∙_)

-- TODO add vertical composition
