{-# OPTIONS --safe #-}
module Correspondences.Powerset where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Base public
open import Correspondences.Decidable

open import Data.Bool as Bool
open import Data.Dec as Dec
open import Data.Empty as ⊥
open import Data.Sum.Base
open import Data.Unit.Instances.HLevel

open import Truncation.Propositional as ∥-∥₁

private variable
  ℓ : Level
  X : Type ℓ
  x y : X

ℙ : Type ℓ → Type (ℓsuc ℓ)
ℙ X = X → Prop _

private variable A B : ℙ X

subst-∈ : (A : ℙ X) → x ＝ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

⊆-refl : (A : ℙ X) → A ⊆ A
⊆-refl _ = id

@0 ℙ-ext : A ⊆ B → B ⊆ A → A ＝ B
ℙ-ext A⊆B B⊆A = fun-ext λ _ → n-ua (prop-extₑ! A⊆B B⊆A)

single : {@(tactic hlevel-tactic-worker) X-set : is-set X} → X → ℙ X
single {X-set} x t = el (x ＝ t) (path-is-of-hlevel′ 1 X-set x t)

infixr 22 _∩_
_∩_ : ℙ X → ℙ X → ℙ X
(A ∩ B) x = el! ((x ∈ A) × (x ∈ B))

infixr 21 _∪_
_∪_ : ℙ X → ℙ X → ℙ X
(A ∪ B) x = el! ((x ∈ A) ⊎₁ (x ∈ B))

⟙ : ℙ X
⟙ _ = el! (Lift _ ⊤)

⟘ : ℙ X
⟘ _ = el! (Lift _ ⊥)

⟘⊆ : ⟘ ⊆ A
⟘⊆ ()

@0 ⊆⟘→⟘ : A ⊆ ⟘ → A ＝ ⟘
⊆⟘→⟘ {A} p = ℙ-ext p (⟘⊆ {A = A})

⟙⊆ : A ⊆ ⟙
⟙⊆ = _


-- decidable subsets

is-complemented : (A : ℙ X) → Type _
is-complemented {X} A = Σ[ A⁻¹ ꞉ ℙ X ] (A ∩ A⁻¹ ⊆ ⟘) × (⟙ ⊆ A ∪ A⁻¹)

is-decidable-subset : (A : ℙ X) → Type _
is-decidable-subset A = Decidable¹ (_∈ A)

is-complemented→is-decidable-subset : (A : ℙ X) → is-complemented A → is-decidable-subset A
is-complemented→is-decidable-subset A (A⁻¹ , int , uni) x =
  ∥-∥₁.rec! [ yes , (λ x∈A⁻¹ → no λ x∈A → lower (int (x∈A , x∈A⁻¹))) ]ᵤ (uni _)

is-decidable-subset→is-complemented : (A : ℙ X) → is-decidable-subset A → is-complemented A
is-decidable-subset→is-complemented {X} A d
  = (λ x → el! (¬ (x ∈ A)))
  , (λ z → lift (z .snd (z .fst)))
  , λ {x} → Dec.rec (λ x∈A _ → ∣ inl x∈A ∣₁) (λ x∈A⁻¹ _ → ∣ inr x∈A⁻¹ ∣₁) (d x)

ℙᵈ : Type ℓ → Type _
ℙᵈ X = Σ[ A ꞉ ℙ X ] is-decidable-subset A

@0 decidable-subobject-classifier : (X → Bool) ≃ ℙᵈ X
decidable-subobject-classifier {X} = iso→equiv $ to , iso (λ pr x → from pr x .fst) ri li where
  to : _
  to ch = (λ x → el (Lift _ (ch x ＝ true)) hlevel!)
        , λ x → Bool.elim {P = λ x → Dec (Lift _ (x ＝ true))}
                  (yes (lift refl)) (no (true≠false ∘ sym ∘ lower)) (ch x)

  from : (pr : ℙᵈ X) (x : X) → Σ[ b ꞉ Bool ] ((b ＝ true) ≃ (x ∈ pr .fst))
  from (A , d) x = Dec.elim (λ x∈A → true , prop-extₑ!
                              (λ _ → x∈A) (λ _ → refl))
                            (λ x∉A → false , prop-extₑ!
                              (λ p → ⊥.rec (false≠true p)) (λ x∈A → ⊥.rec (x∉A x∈A)))
                            (d x)

  ri : _
  ri A = Σ-prop-path! (ℙ-ext (λ {x} → from A x .snd .fst ∘ lower)
                             (λ {x} → lift ∘ Equiv.from (from A x .snd)))

  li : _
  li ch = fun-ext λ x → Bool.elim {P = λ p → from (to λ _ → p) x .fst ＝ p} refl refl (ch x)
