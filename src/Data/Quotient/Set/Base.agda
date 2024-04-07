{-# OPTIONS --safe #-}
module Data.Quotient.Set.Base where

open import Meta.Prelude

data _/_ {ℓ ℓ′} (A : Type ℓ) (R : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  ⦋_⦌      : (a : A) → A / R
  glue/   : (a b : A) (r : R a b) → ⦋ a ⦌ ＝ ⦋ b ⦌
  squash/ : (x y : A / R) (p q : x ＝ y) → p ＝ q

private variable
  ℓ ℓᵃ ℓᵇ ℓᶜ ℓʳ ℓᵖ ℓˢ ℓᵗ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  P : A → Type ℓᵖ
  R : A → A → Type ℓʳ
  S : B → B → Type ℓˢ

instance opaque
  H-Level-/₂ : ∀ {n} → H-Level (2 + n) (A / R)
  H-Level-/₂ = hlevel-basic-instance 2 squash/

elim
  : {A : Type ℓᵃ} {R : A → A → Type ℓʳ} {P : A / R → Type ℓᵖ}
    (P-set : Π[ x ꞉ A / R ] is-set (P x))
    (f : Π[ a ꞉ A ] P ⦋ a ⦌)
  → (∀ a b (r : R a b) → ＜ f a ／ (λ i → P (glue/ a b r i)) ＼ f b ＞)
  → Π[ q ꞉ A / R ] P q
elim _ f _ ⦋ a ⦌ = f a
elim _ f f= (glue/ a b r i) = f= a b r i
elim P-set f f= (squash/ x y p q i j) =
  is-set→squareᴾ (λ i j → P-set (squash/ x y p q i j))
                 (λ _ → g x)     (λ k → g (p k))
                 (λ k → g (q k)) (λ _ → g y)
                 i j
  where g = elim P-set f f=

elim-prop
  : {A : Type ℓᵃ} {R : A → A → Type ℓʳ} {P : A / R → Type ℓᵖ}
    (P-prop : Π[ x ꞉ A / R ] is-prop (P x))
    (f : Π[ a ꞉ A ] P ⦋ a ⦌)
  → Π[ q ꞉ A / R ] P q
elim-prop _ f ⦋ a ⦌ = f a
elim-prop P-prop f (glue/ a b r i) =
  is-prop→pathᴾ (λ k → P-prop (glue/ a b r k)) (f a) (f b) i
elim-prop P-prop f (squash/ x y p q i j) =
  is-prop→squareᴾ (λ i j → P-prop (squash/ x y p q i j))
                  (λ k → g (p k)) (λ _ → g x)
                  (λ k → g (q k)) (λ _ → g y) -- TODO same order as in elim
                  i j
  where g = elim-prop P-prop f

rec : is-set B
    → (f : A → B)
    → (∀ a b → R a b → f a ＝ f b)
    → A / R → B
rec _ f _ ⦋ a ⦌ = f a
rec _ _ f= (glue/ a b r i) = f= a b r i
rec B-set f f= (squash/ x y p q i j) =
  B-set (g x) (g y) (λ k → g (p k)) (λ k → g (q k)) i j
  where g = rec B-set f f=


-- Automation

elim!
  : {A : Type ℓᵃ} {R : A → A → Type ℓʳ} {P : A / R → Type ℓᵖ}
    ⦃ P-set : ∀[ x ꞉ A / R ] H-Level 2 (P x) ⦄
    (f : Π[ a ꞉ A ] P ⦋ a ⦌)
  → (∀ a b (r : R a b) → ＜ f a ／ (λ i → P (glue/ a b r i)) ＼ f b ＞)
  → Π[ q ꞉ A / R ] P q
elim! = elim (λ _ → hlevel 2)

elim-prop!
  : {A : Type ℓᵃ} {R : A → A → Type ℓʳ} {P : A / R → Type ℓᵖ}
    ⦃ P-prop : ∀[ x ꞉ A / R ] H-Level 1 (P x) ⦄
    (f : Π[ a ꞉ A ] P ⦋ a ⦌)
  → Π[ q ꞉ A / R ] P q
elim-prop! = elim-prop λ _ → hlevel 1

elim-prop!²
  : {A : Type ℓᵃ} {R : A → A → Type ℓʳ}
    {B : Type ℓᵇ} {S : B → B → Type ℓˢ}
    {P : A / R → B / S → Type ℓ}
    ⦃ P-prop : ∀ {x y} → H-Level 1 (P x y) ⦄
    (f : Π[ a ꞉ A ] Π[ b ꞉ B ] P ⦋ a ⦌ ⦋ b ⦌)
  → Π[ q₁ ꞉ A / R ] Π[ q₂ ꞉ B / S ] P q₁ q₂
elim-prop!² {P} f = elim-prop! λ a → elim-prop! (f a)

elim-prop!³
  : {A : Type ℓᵃ} {R : A → A → Type ℓʳ}
    {B : Type ℓᵇ} {S : B → B → Type ℓˢ}
    {C : Type ℓᶜ} {T : C → C → Type ℓᵗ}
    {P : A / R → B / S → C / T → Type ℓ}
    ⦃ P-prop : ∀ {x y z} → H-Level 1 (P x y z) ⦄
    (f : Π[ a ꞉ A ] Π[ b ꞉ B ] Π[ c ꞉ C ] P ⦋ a ⦌ ⦋ b ⦌ ⦋ c ⦌)
  → Π[ q₁ ꞉ A / R ] Π[ q₂ ꞉ B / S ] Π[ q₃ ꞉ C / T ] P q₁ q₂ q₃
elim-prop!³ f = elim-prop!² λ a b → elim-prop! (f a b)

rec! : ⦃ B-set : H-Level 2 B ⦄
     → (f : A → B)
     → (∀ a b → R a b → f a ＝ f b)
     → A / R → B
rec! = rec (hlevel 2)

rec² : ⦃ C-set : H-Level 2 C ⦄
     → (f : A → B → C)
     → (∀ x y b → R x y → f x b ＝ f y b)
     → (∀ a x y → S x y → f a x ＝ f a y)
     → A / R → B / S → C
rec² f fa= fb= = rec! (λ a → rec! (f a) (fb= a)) λ a b r →
  fun-ext $ elim-prop! λ x → fa= a b x r
