{-# OPTIONS --safe #-}
module Combinatorics.Power.Decidable where

open import Meta.Prelude
open import Meta.Extensionality

open import Structures.n-Type

open import Logic.Decidability

open import Combinatorics.Power.Base

open import Data.Bool as Bool
open import Data.Dec as Dec
open import Data.Empty as ⊥
open import Data.Reflects.Base as Reflects
open import Data.Sum.Base
open import Data.Truncation.Propositional as ∥-∥₁
open import Data.Unit.Base


private variable
  ℓˣ ℓ : Level
  X : Type ℓˣ
  x y : X

is-complemented : {ℓ : Level} (A : ℙ X ℓ) → Type (level-of-type X ⊔ ℓsuc ℓ)
is-complemented {X} {ℓ} A = Σ[ A⁻¹ ꞉ ℙ X ℓ ] (A ∩ A⁻¹       ⊆ the (ℙ X ℓ) ⊥)
                                           × (the (ℙ X ℓ) ⊤ ⊆ A ∪ A⁻¹)

is-complemented→is-decidable-subset : (A : ℙ X ℓ) → is-complemented A → Decidable A
is-complemented→is-decidable-subset A (A⁻¹ , int , uni) {x} = case uni _ of
  [ yes
  , (λ x∈A⁻¹ → no λ x∈A → int (x∈A , x∈A⁻¹) .lower)
  ]ᵤ

is-decidable-subset→is-complemented : (A : ℙ X ℓ) → Decidable A → is-complemented A
is-decidable-subset→is-complemented {X} A d
  = (λ x → el! (¬ x ∈ A))
  , (λ z → lift (z .snd (z .fst)))
  , Dec.rec (λ x∈A _ → ∣ inl x∈A ∣₁) (λ x∈A⁻¹ _ → ∣ inr x∈A⁻¹ ∣₁) d

ℙᵈ : {ℓ : Level} → Type ℓˣ → Type (ℓˣ ⊔ ℓsuc ℓ)
ℙᵈ {ℓ} X = Σ[ A ꞉ ℙ X ℓ ] Decidable A

@0 decidable-subobject-classifier : {X : 𝒰 ℓ} → (X → Bool) ≃ ℙᵈ X
decidable-subobject-classifier {ℓ} {X} = ≅→≃ $ to , iso (λ pr x → from pr x .fst) ri li where
  to : (X → Bool) → ℙᵈ X
  to ch = (λ x → el! (Lift ℓ ⌞ ch x ⌟)) , auto

  from : (pr : ℙᵈ X) (x : X) → Σ[ b ꞉ Bool ] (⌞ b ⌟ ≃ (x ∈ pr .fst))
  from (A , d) x = Dec.elim (λ x∈A → true  , prop-extₑ! (λ _ → x∈A) (λ _ → oh))
                            (λ x∉A → false , prop-extₑ! (λ ()) λ x∈A → false! (x∉A x∈A)) d

  ri : _
  ri A = ext (λ a → (lower ∙ from A a .snd .fst) , (from A a .snd ⁻¹) #_ ∙ lift) ,ₚ prop!

  li : _
  li ch = fun-ext λ x → Bool.elim {P = λ p → from (to λ _ → p) x .fst ＝ p} refl refl (ch x)
