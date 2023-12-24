{-# OPTIONS --safe #-}
module Data.Nat.Cantor where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Marker

open import Data.Fin.Computational.Base
open import Data.Nat.Base
open import Data.Nat.Order.Base
open import Data.Nat.Properties
open import Data.Nat.Solver

-- see hybrid-agda by Sergey Goncharov
ℕ×ℕ≃ℕ : ℕ × ℕ ≃ ℕ
ℕ×ℕ≃ℕ = iso→equiv $ (π $²_) , iso < π₁⁻¹ , π₂⁻¹ > ri li where
  π : ℕ → ℕ → ℕ
  π 0       0       = 0
  π 0       (suc n) = suc (π 0 n + suc n)
  π (suc m) n       = π m n + suc (m + n)

  π₁⁻¹ π₂⁻¹ : ℕ → ℕ

  π₁⁻¹ 0       = 0
  π₁⁻¹ (suc m) with (π₁⁻¹ m)
  ... | 0     = suc (π₂⁻¹ m)
  ... | suc m = m

  π₂⁻¹ 0 = 0
  π₂⁻¹ (suc n) with (π₁⁻¹ n)
  ... | 0     = 0
  ... | suc _ = suc (π₂⁻¹ n)

  π-suc : ∀ m n → π m (suc n) ＝ suc (π (suc m) n)
  π-suc 0       _ = refl
  π-suc (suc m) n = let ih = π-suc m n in
    ⌜ π m (suc n) ⌝ + suc (m + suc n)                ＝⟨ ap! (π-suc m n) ⟩
    suc (π m n + suc (m + n) + ⌜ suc (m + suc n) ⌝)  ＝⟨ ap! (+-suc-r (suc m) _) ⟩
    suc (π m n + suc (m + n) + suc (suc (m + n)))    ∎

  π-plus : ∀ m n → π m n ＝ π (m + n) 0 + n
  π-plus m 0       = sym $ +-zero-r _ ∙ ap (λ φ → π φ 0) (+-zero-r m)
  π-plus m (suc n) =
    π m (suc n)
      ＝⟨ π-suc m n ⟩
    suc (⌜ π m n ⌝ + suc (m + n))
      ＝⟨ ap! (π-plus m n) ⟩
    suc ⌜ π (m + n) 0 + n + suc (m + n) ⌝
      ＝⟨ ap! ( sym (+-assoc (π (m + n) 0) n (suc (m + n)))
              ∙ ap (π (m + n) 0 +_) nat!
              ∙ +-assoc (π (m + n) 0) (suc (m + n + 0)) n ) ⟩
    suc (⌜ π (m + n) 0 + suc (m + n + 0) ⌝ + n)
      ＝˘⟨ ap¡ (ap (λ φ → π φ 0) (+-suc-r _ n)) ⟩
    suc (π (m + suc n) 0 + n)
      ＝˘⟨ +-suc-r _ n ⟩
    π (m + suc n) 0 + suc n ∎

  π′ : ℕ → ℕ
  π′ 0       = 0
  π′ (suc n) = π′ n + suc n

  π′＝π-0 : ∀ n → π′ n ＝ π n 0
  π′＝π-0 0       = refl
  π′＝π-0 (suc n) =
    ⌜ π′ n ⌝ + suc n     ＝⟨ ap! (π′＝π-0 n) ⟩
    π n 0 + suc ⌜ n ⌝    ＝˘⟨ ap¡ (+-zero-r n) ⟩
    π n 0 + suc (n + 0)  ∎

  ri : < π₁⁻¹ , π₂⁻¹ > is-right-inverse-of (π $²_)
  ri 0       = refl
  ri (suc m) with π₁⁻¹ m | recall π₁⁻¹ m
  ... | 0     | ⟪ p ⟫ =
    let ν = π₂⁻¹ m
        ih = subst (λ φ → π φ ν ＝ m) p (ri m) in
    π ν 0 + suc ⌜ ν + 0 ⌝  ＝⟨ ap! nat! ⟩
    π ν 0 + suc ν          ＝⟨ +-suc-r _ _ ⟩
    suc ⌜ π ν 0 + ν ⌝      ＝⟨ ap! (sym (π-plus 0 ν) ∙ ih) ⟩
    suc m                  ∎
  ... | suc k | ⟪ p ⟫ =
    let ν = π₂⁻¹ m
        ih = subst (λ φ → π φ ν ＝ m) p (ri m) in
    π k (suc ν)                  ＝⟨ π-suc k ν ⟩
    suc ⌜ π k ν + suc (k + ν) ⌝  ＝⟨ ap! ih ⟩
    suc m                        ∎

  li : < π₁⁻¹ , π₂⁻¹ > is-left-inverse-of (π $²_)
  li (m , n) = {!!}
