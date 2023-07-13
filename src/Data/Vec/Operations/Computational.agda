{-# OPTIONS --safe #-}
module Data.Vec.Operations.Computational where

open import Foundations.Base
open import Foundations.Equiv

open import Correspondences.Erased

open import Data.FinSub.Base
open import Data.List.Base
open import Data.List.Operations

open import Data.Vec.Base public

private variable
  ℓ : Level
  A : Type ℓ
  @0 n : ℕ

tabulate : {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = 0}     _ = []
tabulate {n = suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

opaque
  unfolding Fin
  lookup : Vec A n → Fin n → A
  lookup (x ∷ _) (0 , _) = x
  lookup (x ∷ xs) (suc k , ∣ p ∣ᴱ) = lookup xs (k , ∣ p ∣ᴱ)

  replace : Fin n → A → Vec A n → Vec A n
  replace (zero , _) y (_ ∷ xs) = y ∷ xs
  replace (suc k , ∣ p ∣ᴱ) y (x ∷ xs) = x ∷ replace (k , ∣ p ∣ᴱ) y xs

vec→list : Vec A n → Σ[ xs ꞉ List A ] ∥ length xs ＝ n ∥ᴱ
vec→list [] = [] , ∣ refl ∣ᴱ
vec→list (x ∷ xs) =
  let xs′ , ∣ p ∣ᴱ = vec→list xs
  in x ∷ xs′ , ∣ ap suc p ∣ᴱ

list→vec : (xs : List A) → Σ[ len ꞉ ℕ ] Vec A len × (length xs ＝ len)
list→vec [] = 0 , [] , refl
list→vec (x ∷ xs) =
  let len′ , xs′ , p = list→vec xs
  in suc len′ , x ∷ xs′ , ap suc p

opaque
  unfolding Fin lookup
  vec-fun-equiv : {n : ℕ} → Vec A n ≃ (Fin n → A)
  vec-fun-equiv {n} = iso→equiv (lookup , iso tabulate (lemma₁ {n = n}) lemma₂) where
    lemma₁ : {n : ℕ} → Π[ f ꞉ (Fin n → A) ] (lookup {n = n} (tabulate f) ＝ f)
    lemma₁ {n = zero} _ = fun-ext λ()
    lemma₁ {n = suc n} f = fun-ext λ where
      (0 , _) → refl
      (suc k , p) → happly (lemma₁ {n = n} _) (k , p)

    lemma₂ : {n : ℕ} → Π[ xs ꞉ Vec A n ] (tabulate (lookup xs) ＝ xs)
    lemma₂ {n = 0} [] = refl
    lemma₂ {n = suc n} (x ∷ xs) = ap (x ∷_) (lemma₂ _)
