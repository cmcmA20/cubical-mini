{-# OPTIONS --safe #-}
module Foundations.Path where

open import Foundations.Prelude

private variable
  ℓ : Level
  A B : Type ℓ
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


-- path concatenation has all the usual properties
-- path space has a groupoid structure

∙-filler₂ : (q : x ＝ y) (r : y ＝ z)
          → Square q (q ∙ r) r refl
∙-filler₂ q r k i = hcomp (k ∨ ∂ i) λ where
  l (l = i0) → q (i ∨ k)
  l (k = i1) → r (l ∧ i)
  l (i = i0) → q k
  l (i = i1) → r l

∙-id-l : (p : x ＝ y) → refl ∙ p ＝ p
∙-id-l p = sym (∙-filler′ refl p)

∙-id-r : (p : x ＝ y) → p ∙ refl ＝ p
∙-id-r p = sym (∙-filler p refl)

∙-assoc : (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
        → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
∙-assoc p q r i = ∙-filler p q i ∙ ∙-filler′ q r (~ i)

∙-inv-l : (p : x ＝ y) → sym p ∙ p ＝ refl
∙-inv-l {y} p i j = hcomp (∂ j ∨ i) λ where
  k (j = i0) → y
  k (j = i1) → p (k ∨ i)
  k (i = i1) → y
  k (k = i0) → p (~ j ∨ i)

∙-inv-r : (p : x ＝ y) → p ∙ sym p ＝ refl
∙-inv-r p = ∙-inv-l (sym p)

∙-cancel-l : (p : x ＝ y) (q : y ＝ z)
           → (sym p ∙ p ∙ q) ＝ q
∙-cancel-l {y} p q i j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → p (i ∨ ~ j)
  k (i = i0) → ∙-filler (sym p) (p ∙ q) k j
  k (i = i1) → q (j ∧ k)
  k (j = i0) → y
  k (j = i1) → ∙-filler₂ p q i k

∙-cancel-r : (p : x ＝ y) (q : z ＝ y)
           → ((p ∙ sym q) ∙ q) ＝ p
∙-cancel-r q p = sym $ ∙-unique _ λ i j →
  ∙-filler q (sym p) (~ i) j

commutes→square : {p : w ＝ x} {q : w ＝ y} {s : x ＝ z} {r : y ＝ z}
                → p ∙ s ＝ q ∙ r
                → Square p q s r
commutes→square {p} {q} {s} {r} fill i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → fill j i
    k (i = i0) → q (k ∧ j)
    k (i = i1) → s (~ k ∨ j)
    k (j = i0) → ∙-filler p s (~ k) i
    k (j = i1) → ∙-filler₂ q r k i

square→commutes : {p : w ＝ x} {q : w ＝ y} {s : x ＝ z} {r : y ＝ z}
                → Square p q s r
                → p ∙ s ＝ q ∙ r
square→commutes {p} {q} {s} {r} fill i j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → fill j i
  k (i = i0) → ∙-filler p s k j
  k (i = i1) → ∙-filler₂ q r (~ k) j
  k (j = i0) → q (~ k ∧ i)
  k (j = i1) → s (k ∨ i)

∙-cancel′-l : (p : x ＝ y) (q r : y ＝ z)
            → p ∙ q ＝ p ∙ r
            → q ＝ r
∙-cancel′-l p q r sq =
     sym (∙-cancel-l p q)
  ∙∙ ap (sym p ∙_) sq
  ∙∙ ∙-cancel-l p r

∙-cancel′-r : (p : y ＝ z) (q r : x ＝ y)
            → q ∙ p ＝ r ∙ p
            → q ＝ r
∙-cancel′-r p q r sq =
     sym (∙-cancel-r q (sym p))
  ∙∙ ap (_∙ sym p) sq
  ∙∙ ∙-cancel-r r (sym p)

homotopy-invert : {f : A → A}
                → (H : (x : A) → f x ＝ x) {x : A}
                → H (f x) ＝ ap f (H x)
homotopy-invert {f} H {x} i j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → H x       (j ∧ i)
  k (j = i0) → H (f x)   (~ k)
  k (j = i1) → H x       (~ k ∧ i)
  k (i = i0) → H (f x)   (~ k ∨ j)
  k (i = i1) → H (H x j) (~ k)


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
