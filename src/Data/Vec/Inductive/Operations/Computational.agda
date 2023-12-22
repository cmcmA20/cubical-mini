{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Operations.Computational where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Fin.Computational.Base
open import Data.List.Base
open import Data.List.Operations
  hiding (lookup)

open import Data.Vec.Inductive.Base public

private variable
  ℓ : Level
  A : Type ℓ
  @0 n : ℕ

tabulate : {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = 0}     _ = []
tabulate {n = suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

lookup : Vec A n → Fin n → A
lookup (x ∷ _)  (mk-fin 0)             = x
lookup (_ ∷ xs) (mk-fin (suc k) {(b)}) = lookup xs (mk-fin k {b})

replace : Fin n → A → Vec A n → Vec A n
replace (mk-fin 0)             y (_ ∷ xs) = y ∷ xs
replace (mk-fin (suc k) {(b)}) y (x ∷ xs) = x ∷ replace (mk-fin k {b}) y xs

vec→list : Vec A n → Σ[ xs ꞉ List A ] Erased (length xs ＝ n)
vec→list [] = [] , erase refl
vec→list (x ∷ xs) =
  let xs′ , erase p = vec→list xs
  in x ∷ xs′ , erase (ap suc p)

list→vec : (xs : List A) → Σ[ len ꞉ ℕ ] Vec A len × (length xs ＝ len)
list→vec [] = 0 , [] , refl
list→vec (x ∷ xs) =
  let len′ , xs′ , p = list→vec xs
  in suc len′ , x ∷ xs′ , ap suc p

vec-fun-equiv : {n : ℕ} → Vec A n ≃ (Fin n → A)
vec-fun-equiv {n} = iso→equiv (lookup , iso tabulate (lemma₁ {n = n}) lemma₂) where
  lemma₁ : {n : ℕ} → Π[ f ꞉ (Fin n → A) ] (lookup {n = n} (tabulate f) ＝ f)
  lemma₁ {n = zero} _ = fun-ext λ()
  lemma₁ {n = suc n} f = fun-ext λ where
    (mk-fin 0)       → refl
    (mk-fin (suc k)) → happly (lemma₁ {n = n} _) (mk-fin k)

  lemma₂ : {n : ℕ} → Π[ xs ꞉ Vec A n ] (tabulate (lookup xs) ＝ xs)
  lemma₂ {n = 0} [] = refl
  lemma₂ {n = suc n} (x ∷ xs) = ap (x ∷_) (lemma₂ _)
