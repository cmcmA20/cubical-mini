{-# OPTIONS --safe #-}
module Truncation.Propositional.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Functions.Constant
open import Functions.Embedding
open import Functions.Surjection

open import Truncation.Propositional.Base public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  f : A → B
  C : Type ℓ″

elim² : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ″}
      → (∀ x y → is-prop (P x y))
      → (∀ x y → P ∣ x ∣₁ ∣ y ∣₁)
      → ∀ x y → P x y
elim² {A} {B} {P} P-prop work x y = go x y where
  go : ∀ x y → P x y
  go ∣ x ∣₁ ∣ y ∣₁ = work x y
  go ∣ x ∣₁ (squash₁ y y′ i) =
    is-prop→pathP (λ i → P-prop ∣ x ∣₁ (squash₁ y y′ i))
                  (go ∣ x ∣₁ y) (go ∣ x ∣₁ y′) i

  go (squash₁ x y i) z =
    is-prop→pathP (λ i → P-prop (squash₁ x y i) z)
                  (go x z) (go y z) i

rec² : is-prop C
     → (A → B → C)
     → (x : ∥ A ∥₁) (y : ∥ B ∥₁) → C
rec² C-prop = elim² (λ _ _ → C-prop)

rec!
  : {@(tactic hlevel-tactic-worker) B-prop : is-prop B}
  → (A → B)
  → (x : ∥ A ∥₁) → B
rec! {B-prop} = elim (λ _ → B-prop)

rec²! : {@(tactic hlevel-tactic-worker) C-prop : is-prop C}
      → (A → B → C)
      → (x : ∥ A ∥₁) (y : ∥ B ∥₁) → C
rec²! {C-prop} = rec² C-prop

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

elim²! : {P : ∥ A ∥₁ → ∥ B ∥₁ → Type ℓ″}
       → {@(tactic hlevel-tactic-worker) P-prop : ∀ x y → is-prop (P x y)}
       → (∀ x y → P ∣ x ∣₁ ∣ y ∣₁)
       → ∀ x y → P x y
elim²! {P-prop} = elim² P-prop

universal : is-prop B → (∥ A ∥₁ → B) ≃ (A → B)
universal {B} {A} B-prop = iso→equiv $ inc′ , iso rec′ (λ _ → refl) beta where
  instance _ = B-prop
  inc′ : (x : ∥ A ∥₁ → B) → A → B
  inc′ f x = f ∣ x ∣₁

  rec′ : (f : A → B) → ∥ A ∥₁ → B
  rec′ f ∣ x ∣₁ = f x
  rec′ f (squash₁ x y i) = is-prop-β B-prop (rec′ f x) (rec′ f y) i

  beta : rec′ is-left-inverse-of inc′
  beta f = fun-ext $ elim! λ _ → refl

is-prop→equiv-∥-∥₁ : is-prop A → A ≃ ∥ A ∥₁
is-prop→equiv-∥-∥₁ A-prop = prop-extₑ! ∣_∣₁ proj!
  where instance _ = A-prop

is-prop≃equiv-∥-∥₁ : is-prop A ≃ (A ≃ ∥ A ∥₁)
is-prop≃equiv-∥-∥₁ {A} = prop-extₑ! is-prop→equiv-∥-∥₁ (λ e → is-of-hlevel-≃ 1 e hlevel!)

corestriction : (f : A → B) → (A → Im f)
corestriction f x = f x , ∣ x , refl ∣₁

corestriction-is-surjective : is-surjective (corestriction f)
corestriction-is-surjective (_ , p) = map (second Σ-prop-path!) p

dom-is-set→image-is-set
  : is-set B → {f : A → B} → is-set (Im f)
dom-is-set→image-is-set B-set = Σ-is-of-hlevel 2 B-set λ _ → ∥-∥₁-is-of-hlevel 1

is-constant→image-is-prop
  : is-set B → {f : A → B} → 2-Constant f → is-prop (Im f)
is-constant→image-is-prop B-set {f} f-const = is-prop-η λ (a , x) (b , y) →
  Σ-prop-path! $ elim²! (λ { (f*a , p) (f*b , q) → sym p ∙∙ f-const f*a f*b ∙∙ q }) x y
  where instance _ = B-set

-- TODO if codomain is an n-type, we should require f to be n-constant
-- write a generic recursor
rec-set : {f : A → B}
        → 2-Constant f
        → is-set B
        → ∥ A ∥₁ → B
rec-set f-const B-set = fst ∘ elim
  (λ _ → is-constant→image-is-prop B-set f-const) (corestriction _)

Σ-∥-∥₁-over-prop
  : {B : A → Type ℓ′} → is-prop A
  → Σ[ a ꞉ A ] ∥ B a ∥₁ ≃ ∥ Σ[ a ꞉ A ] B a ∥₁
Σ-∥-∥₁-over-prop A-prop = prop-extₑ!
  (λ x → map (x .fst ,_) (x .snd))
  (rec! (second ∣_∣₁)) where instance _ = A-prop


_factors-through_
  : (f : A → C) (B : Type (level-of-type A ⊔ level-of-type C)) → _
_factors-through_ {A} {C} f B = Σ[ ρ ꞉ (A ↠ B) ] Σ[ ι ꞉ (B ↪ C) ] (f ＝ ι .fst ∘ ρ .fst)

Factorization : (f : A → C) → _
Factorization f = Σ[ M ꞉ Type _ ] f factors-through M

image-factorization : f factors-through Im f
image-factorization {f} =
  (corestriction f , corestriction-is-surjective) , (fst , subset-proj-is-embedding hlevel!) , refl
