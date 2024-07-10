{-# OPTIONS --safe #-}
module Data.List.Container where

open import Foundations.Prelude

open import Meta.Notation.Brackets

open import Data.List.Base
  renaming (List to Listⁱ)
open import Data.Nat.Base
open import Data.Fin.Base as Fin

open import Data.Container

List : {ℓ : Level} → Type ℓ → Type ℓ
List = ⟦ ℕ ▶ Fin ⟧

private variable
  ℓ : Level
  A : Type ℓ
  x : A
  xs : List A
  xsⁱ : Listⁱ A

cons : A → List A → List A
cons a (n , _) .fst = suc n
cons a (_ , f) .snd fzero    = a
cons a (_ , f) .snd (fsuc k) = f k

list→container : Listⁱ A → List A
list→container []       = 0 , λ ()
list→container (x ∷ xs) = cons x (list→container xs)

container→list′ : (n : ℕ) (f : Fin n → A) → Listⁱ A
container→list′ 0       _ = []
container→list′ (suc n) f = f fzero ∷ container→list′ n (f ∘ fsuc)

list→container→list : (xs : Listⁱ A) → container→list′ $² (list→container xs) ＝ xs
list→container→list []       = refl
list→container→list (x ∷ xs) = ap (x ∷_) (list→container→list xs)

container→list→container : (n : ℕ) (f : Fin n → A) → list→container (container→list′ n f) ＝ (n , f)
container→list→container 0       _ = Σ-path refl (fun-ext λ ())
container→list→container (suc n) f = Σ-path (ap (suc ∘ fst) ih) $ fun-ext go
  where
  ih = container→list→container n (f ∘ fsuc)
  go : (k : Fin _) → _
  go fzero    = transport-refl _
  go (fsuc k) = happly (from-pathᴾ (ap snd ih)) k

list-container-equiv : Listⁱ A ≃ List A
list-container-equiv =
  ≅→≃ (list→container , iso (container→list′ $²_) (container→list→container $²_) list→container→list)
