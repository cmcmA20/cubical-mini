{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Properties where

open import Meta.Prelude

open import Data.Empty.Base
open import Data.Fin.Inductive.Base as Fin
open import Data.List.Base
open import Data.List.Instances.Container
open import Data.Nat.Path
open import Data.Reflects.Base
open import Data.Vec.Inductive.Base public
open import Data.Vec.Inductive.Operations

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  m n : ℕ

cast : m ＝ n → Vec A m → Vec A n
cast {0}     {0}     _ xs = xs
cast {0}     {suc n} p = false! p
cast {suc m} {0}     p = false! p
cast {suc m} {suc n} p (x ∷ xs) = x ∷ cast (suc-inj p) xs

vec-fun-equiv : Vec A n ≃ (Fin n → A)
vec-fun-equiv = ≅→≃ $ iso lookup tabulate (fun-ext lemma₁) (fun-ext lemma₂) where
  lemma₁ : Π[ f ꞉ (Fin n → A) ] (lookup (tabulate f) ＝ f)
  lemma₁ {0}     _ = fun-ext λ()
  lemma₁ {suc n} f = fun-ext λ where
    fzero    → refl
    (fsuc k) → lemma₁ _ $ₚ k

  lemma₂ : Π[ xs ꞉ Vec A n ] (tabulate (lookup xs) ＝ xs)
  lemma₂ {n = 0}     []       = refl
  lemma₂ {n = suc n} (x ∷ xs) = ap (x ∷_) (lemma₂ _)

list≃vec : List A ≃ Σ[ n ꞉ ℕ ] Vec A n
list≃vec
  = list≃cont
  ∙ Σ-ap-snd (λ _ → (vec-fun-equiv ∙ Π-dom-≃ Fin.default≃inductive) ⁻¹)
