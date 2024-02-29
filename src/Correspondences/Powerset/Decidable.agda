{-# OPTIONS --safe #-}
module Correspondences.Powerset.Decidable where

open import Foundations.Base
  hiding (Σ-syntax; Π-syntax; ∀-syntax)
open import Foundations.Equiv

open import Meta.Membership
open import Meta.Search.Decidable
open import Meta.Search.HLevel

open import Structures.n-Type

open import Correspondences.Decidable
open import Correspondences.Powerset.Base public

open import Data.Bool as Bool
open import Data.Dec as Dec
open import Data.Empty as ⊥
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Instances.Decidable

open import Truncation.Propositional as ∥-∥₁


private variable
  ℓ : Level
  X : Type ℓ
  x y : X

is-complemented : (A : ℙ X) → Type _
is-complemented {X} A = Σ[ A⁻¹ ꞉ ℙ X ] (A ∩ A⁻¹ ⊆ ⟘) × (⟙ ⊆ A ∪ A⁻¹)

is-decidable-subset : (A : ℙ X) → Type (level-of-type X)
is-decidable-subset {X} A = Decidableⁿ {1} (λ (x : X) → x ∈ A)

is-complemented→is-decidable-subset : (A : ℙ X) → is-complemented A → is-decidable-subset A
is-complemented→is-decidable-subset A (A⁻¹ , int , uni) x =
  ∥-∥₁.rec! [ yes , (λ x∈A⁻¹ → no λ x∈A → lower (int (x∈A , x∈A⁻¹))) ]ᵤ (uni _)

is-decidable-subset→is-complemented : (A : ℙ X) → is-decidable-subset A → is-complemented A
is-decidable-subset→is-complemented {X} A d
  = (λ x → el! (¬ (x ∈ A)))
  , (λ z → lift (z .snd (z .fst)))
  , Dec.rec (λ x∈A _ → ∣ inl x∈A ∣₁) (λ x∈A⁻¹ _ → ∣ inr x∈A⁻¹ ∣₁) (d _)

ℙᵈ : Type ℓ → Type _
ℙᵈ X = Σ[ A ꞉ ℙ X ] is-decidable-subset A

@0 decidable-subobject-classifier : (X → Bool) ≃ ℙᵈ X
decidable-subobject-classifier {X} = iso→equiv $ to , iso (λ pr x → from pr x .fst) ri li where
  to : _
  to ch = (λ x → el (Lift _ ⟦ ch x ⟧ᵇ) (Bool.elim {P = λ b → is-prop (Lift _ ⟦ b ⟧ᵇ)} hlevel! hlevel! (ch x)))
        , λ x → Bool.elim {P = λ x → Dec (Lift _ ⟦ x ⟧ᵇ)} decide! decide! (ch x)

  from : (pr : ℙᵈ X) (x : X) → Σ[ b ꞉ Bool ] (⟦ b ⟧ᵇ ≃ (x ∈ pr .fst))
  from (A , d) x = Dec.elim (λ x∈A → true  , prop-extₑ! (λ _ → x∈A) _)
                            (λ x∉A → false , prop-extₑ! (⊥.rec $ᴱ_) x∉A) (d x)

  ri : _
  ri A = Σ-prop-path! (ℙ-ext (from A _ .snd .fst ∘ lower) (lift ∘ Equiv.from (from A _ .snd)))

  li : _
  li ch = fun-ext λ x → Bool.elim {P = λ p → from (to λ _ → p) x .fst ＝ p} refl refl (ch x)
