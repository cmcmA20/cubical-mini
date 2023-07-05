{-# OPTIONS --safe #-}
module Truncation.Propositional.Properties where

open import Foundations.Base
open import Foundations.Sigma
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Truncation.Propositional.Base public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

elim₂ : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ″}
      → (∀ x y → is-prop (P x y))
      → (∀ x y → P ∣ x ∣₁ ∣ y ∣₁)
      → ∀ x y → P x y
elim₂ {A} {B} {P} P-prop work x y = go x y where
  go : ∀ x y → P x y
  go ∣ x ∣₁ ∣ y ∣₁ = work x y
  go ∣ x ∣₁ (squash₁ y y′ i) =
    is-prop→pathP (λ i → P-prop ∣ x ∣₁ (squash₁ y y′ i))
                  (go ∣ x ∣₁ y) (go ∣ x ∣₁ y′) i

  go (squash₁ x y i) z =
    is-prop→pathP (λ i → P-prop (squash₁ x y i) z)
                  (go x z) (go y z) i

rec₂ : is-prop C
     → (A → B → C)
     → (x : ∥ A ∥₁) (y : ∥ B ∥₁) → C
rec₂ C-prop = elim₂ (λ _ _ → C-prop)

rec!
  : {@(tactic hlevel-tactic-worker) B-prop : is-prop B}
  → (A → B)
  → (x : ∥ A ∥₁) → B
rec! {B-prop} = elim (λ _ → B-prop)

rec₂! : {@(tactic hlevel-tactic-worker) C-prop : is-prop C}
      → (A → B → C)
      → (x : ∥ A ∥₁) (y : ∥ B ∥₁) → C
rec₂! {C-prop} = rec₂ C-prop

elim!
  : {P : ∥ A ∥₁ → Type ℓ′}
    {@(tactic hlevel-tactic-worker) P-prop : ∀{a} → is-prop (P a)}
  → Π[ a ꞉ A ] P ∣ a ∣₁
  → (x : ∥ A ∥₁) → P x
elim! {P-prop} = elim (λ _ → P-prop)

proj!
  : {@(tactic hlevel-tactic-worker) A-prop : is-prop A}
  → ∥ A ∥₁ → A
proj! {A-prop} = rec A-prop id

elim₂! : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ″}
       → {@(tactic hlevel-tactic-worker) P-prop : ∀ x y → is-prop (P x y)}
       → (∀ x y → P ∣ x ∣₁ ∣ y ∣₁)
       → ∀ x y → P x y
elim₂! {A} {B} {P} {P-prop} = elim₂ P-prop

opaque
  unfolding is-of-hlevel
  universal : is-prop B → (∥ A ∥₁ → B) ≃ (A → B)
  universal {B} {A} B-prop = iso→equiv (inc′ , iso rec′ (λ _ → refl) beta) where
    inc′ : (x : ∥ A ∥₁ → B) → A → B
    inc′ f x = f ∣ x ∣₁

    rec′ : (f : A → B) → ∥ A ∥₁ → B
    rec′ f ∣ x ∣₁ = f x
    rec′ f (squash₁ x y i) = B-prop (rec′ f x) (rec′ f y) i

    beta : rec′ is-left-inverse-of inc′
    beta f = fun-ext $ elim (λ _ → is-prop→is-set B-prop _ _) (λ _ → refl)

is-prop→equiv-∥-∥₁ : is-prop A → A ≃ ∥ A ∥₁
is-prop→equiv-∥-∥₁ A-prop =
  prop-extₑ A-prop ∥-∥₁-is-prop ∣_∣₁ (elim (λ _ → A-prop) id)

is-prop≃equiv-∥-∥₁ : is-prop A ≃ (A ≃ ∥ A ∥₁)
is-prop≃equiv-∥-∥₁ {A} =
  prop-extₑ is-prop-is-prop eqv-prop is-prop→equiv-∥-∥₁ inv
  where opaque
    unfolding is-of-hlevel
    inv : (A ≃ ∥ A ∥₁) → is-prop A
    inv eqv = is-equiv→is-of-hlevel 1 ((eqv ₑ⁻¹) .fst) ((eqv ₑ⁻¹) .snd) squash₁

    eqv-prop : is-prop (A ≃ ∥ A ∥₁)
    eqv-prop x y = Σ-path (λ i p → squash₁ (x .fst p) (y .fst p) i)
                          (is-equiv-is-prop _ _ _)

image-lift : (f : A → B) → (A → image f)
image-lift f x = f x , ∣ x , refl ∣₁

opaque
  unfolding is-of-hlevel
  is-constant→image-is-prop
    : is-set B
    → (f : A → B) → (∀ x y → f x ＝ f y) → is-prop (image f)
  is-constant→image-is-prop bset f f-const (a , x) (b , y) =
    Σ-prop-path (λ _ → squash₁)
      (elim₂ (λ _ _ → bset _ _)
        (λ { (f*a , p) (f*b , q) → sym p ∙∙ f-const f*a f*b ∙∙ q }) x y)

-- TODO if codomain is an n-type, we should require f to be n-constant
-- write a generic recursor
rec-set : (f : A → B)
        → (∀ x y → f x ＝ f y)
        → is-set B
        → ∥ A ∥₁ → B
rec-set {A} {B} f f-const B-set x =
  elim {P = λ _ → image f}
    (λ _ → is-constant→image-is-prop B-set f f-const) (image-lift f) x .fst
