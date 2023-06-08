{-# OPTIONS --safe #-}
module Structures.Finite where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Sigma

open import Data.Nat.Path
open import Data.Nat.Instances.Discrete

open import Meta.Discrete
open import Meta.Reflection.HLevel

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

open import Data.Fin.Properties
open import Data.Fin.Instances.Discrete

private variable
  ℓ : Level
  A : Type ℓ

Fin-ordered : Type ℓ → Type ℓ
Fin-ordered A = Σ[ n ꞉ ℕ ] A ≃ Fin n

fin-ordered-is-set : is-set (Fin-ordered A)
fin-ordered-is-set =
  Σ-is-of-hlevel 2 hlevel! (λ _ → ≃-is-of-hlevel-right-suc 1 hlevel!)

is-fin-set : Type ℓ → Type ℓ
is-fin-set A = Σ[ n ꞉ ℕ ] ∥ A ≃ Fin n ∥₁

is-fin-set-is-prop : is-prop (is-fin-set A)
is-fin-set-is-prop (m , ∣p∣₁) (n , ∣q∣₁) =
  Σ-prop-path-equiv hlevel! .fst $
    ∥-∥₁.elim₂ (λ _ _ → ℕ-is-set m n)
               (λ p q → fin-injective ((p ₑ⁻¹) ∙ₑ q))
               ∣p∣₁
               ∣q∣₁

is-fin-set→is-set : is-fin-set A → is-set A
is-fin-set→is-set (_ , ∣e∣₁) =
  ∥-∥₁.rec (is-of-hlevel-is-prop 2) (λ e → is-of-hlevel-≃ 2 e hlevel!) ∣e∣₁

fin-ordered→is-fin-set : Fin-ordered A → is-fin-set A
fin-ordered→is-fin-set (n , e) = n , ∣ e ∣₁
