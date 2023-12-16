{-# OPTIONS --safe #-}
module Foundations.Path.Base where

open import Foundations.Base

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

  ∙′-filler-r : (p : x ＝ y) (q : y ＝ z)
              →  y  ̇      q       ̇ z
                     ┌─    ̇   ─┐

             sym p   │    _    │   refl

                     └─    ̇   ─┘
                 x  ̇    p ∙′ q    ̇ z
  ∙′-filler-r p q = ∙∙-filler p q refl

  -- From this, we can show that these two notions of composition are the same
  ∙＝∙′ : (p : x ＝ y) (q : y ＝ z) → p ∙ q ＝ p ∙′ q
  ∙＝∙′ p q j = ∙∙-unique p q refl (p ∙ q , ∙-filler-r p q) (p ∙′ q , ∙′-filler-r p q) j .fst

  -- We could define double composition with left side `refl`
  -- (classic cubical library way)
  infixr 30 _∙″_
  _∙″_ : x ＝ y → y ＝ z → x ＝ z
  p ∙″ q = refl ∙∙ p ∙∙ q

  ∙″-filler-l : (p : x ＝ y) (q : y ＝ z)
              →  x  ̇      p      ̇ y
                     ┌─    ̇   ─┐

              refl   │    _    │   q

                     └─    ̇   ─┘
                 x  ̇    p ∙″ q    ̇ z
  ∙″-filler-l = ∙∙-filler refl

  ∙＝∙″ : (p : x ＝ y) (q : y ＝ z) → p ∙ q ＝ p ∙″ q
  ∙＝∙″ p q j = ∙∙-unique refl p q (p ∙ q , ∙-filler-l p q) (p ∙″ q , ∙″-filler-l p q) j .fst


opaque
  unfolding _∙_
  sym-∙ : (p : x ＝ y) (q : y ＝ z) → sym (p ∙ q) ＝ sym q ∙ sym p
  sym-∙ p q _ j = (p ∙ q) (~ j)


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
    → (p : a₀ ＝ a₀′) (pq : ＜ a₀′ ／ A ＼ a₁ ＞) (q : a₁ ＝ a₁′)
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


opaque
  unfolding _∙_
  infixr 30 _∙ᴾ_
  _∙ᴾ_ : {B : A → Type ℓ′} {x y z : A} {x′ : B x} {y′ : B y} {z′ : B z} {p : x ＝ y} {q : y ＝ z}
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
  _∙ₕ_ = apP² λ _ → _∙_

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
