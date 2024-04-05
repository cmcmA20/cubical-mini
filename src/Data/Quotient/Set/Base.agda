{-# OPTIONS --safe #-}
module Data.Quotient.Set.Base where

open import Meta.Prelude

data _/_ {ℓ ℓ′} (A : Type ℓ) (R : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  ⦋_⦌      : (a : A) → A / R
  glue/   : (a b : A) (r : R a b) → ⦋ a ⦌ ＝ ⦋ b ⦌
  squash/ : (x y : A / R) (p q : x ＝ y) → p ＝ q

private variable
  ℓᵃ ℓᵇ ℓʳ ℓᵖ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  P : A → Type ℓᵖ
  R : A → A → Type ℓʳ

instance
  H-Level-/₂ : ∀ {n} → H-Level (2 + n) (A / R)
  H-Level-/₂ = hlevel-basic-instance 2 $ is-set-η squash/

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

rec : is-set B
    → (f : A → B)
    → (∀ a b → R a b → f a ＝ f b)
    → A / R → B
rec _ f _ ⦋ a ⦌ = f a
rec _ _ f= (glue/ a b r i) = f= a b r i
rec B-set f f= (squash/ x y p q i j) =
  is-set-β B-set (g x) (g y) (λ k → g (p k)) (λ k → g (q k)) i j
  where g = rec B-set f f=
