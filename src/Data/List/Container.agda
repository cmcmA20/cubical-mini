{-# OPTIONS --safe #-}
module Data.List.Container where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Sigma

open import Containers.List.Base
open import Data.List.Base
open import Data.Nat.Base
open import Data.Fin.Sum

private variable
  ℓ : Level
  A : Type ℓ

list→container : List A → ⟦ ListC ⟧ A
list→container []       = 0 , λ ()
list→container (x ∷ xs) with list→container xs
... | n , f = suc n , λ where
  fzero    → x
  (fsuc k) → f k

container→list′ : (n : ℕ) (f : Fin n → A) → List A
container→list′ 0       _ = []
container→list′ (suc n) f = f fzero ∷ container→list′ n (f ∘ fsuc)

list→container→list : (xs : List A) → container→list′ $₂ (list→container xs) ＝ xs
list→container→list []       = refl
list→container→list (x ∷ xs) = ap (x ∷_) (list→container→list xs)

container→list→container : (n : ℕ) (f : Fin n → A) → list→container (container→list′ n f) ＝ (n , f)
container→list→container 0       _ = Σ-path refl (fun-ext λ () )
container→list→container (suc n) f =
  let ih = container→list→container n (f ∘ fsuc)
  in Σ-path (ap (suc ∘ fst) ih) $ fun-ext λ where
       fzero    → transport-refl _
       (fsuc k) → ap (_$ k) (from-pathP (ap snd ih))

list-container-equiv : List A ≃ ⟦ ListC ⟧ A
list-container-equiv =
  iso→equiv (list→container , iso (container→list′ $₂_) (container→list→container $₂_) list→container→list)
