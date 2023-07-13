{-# OPTIONS --safe #-}
module Data.Vec.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Sigma
open import Foundations.Pi

open import Data.Empty.Base
open import Data.Fin.Base
open import Data.FinSum.Path
  using (sum-fin≃finⁱ)
open import Data.List.Base
  renaming (List to Listⁱ)
open import Data.List.Container
open import Data.Nat.Path
open import Data.Vec.Base public
open import Data.Vec.Operations.Inductive

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  m n : ℕ

cast : m ＝ n → Vec A m → Vec A n
cast {0}     {0}     _ xs = xs
cast {0}     {suc n} p = absurd (suc≠zero (sym p))
cast {suc m} {0}     p = absurd (suc≠zero p)
cast {suc m} {suc n} p (x ∷ xs) = x ∷ cast (suc-inj p) xs

vec-fun-equiv : Vec A n ≃ (Fin n → A)
vec-fun-equiv = iso→equiv (lookup , iso tabulate lemma₁ lemma₂) where
  lemma₁ : Π[ f ꞉ (Fin n → A) ] (lookup (tabulate f) ＝ f)
  lemma₁ {0}     _ = fun-ext λ()
  lemma₁ {suc n} f = fun-ext λ where
    fzero    → refl
    (fsuc k) → happly (lemma₁ _) k

  lemma₂ : Π[ xs ꞉ Vec A n ] (tabulate (lookup xs) ＝ xs)
  lemma₂ {n = 0}     []       = refl
  lemma₂ {n = suc n} (x ∷ xs) = ap (x ∷_) (lemma₂ _)

list≃vec : Listⁱ A ≃ (Σ[ n ꞉ ℕ ] Vec A n)
list≃vec
  =  list-container-equiv
  ∙ₑ Σ-ap-snd (λ _ → (vec-fun-equiv ∙ₑ Π-dom-≃ sum-fin≃finⁱ) ₑ⁻¹)
