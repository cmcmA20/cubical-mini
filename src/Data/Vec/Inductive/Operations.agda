{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Operations where

open import Foundations.Base

open import Data.Bool
open import Data.Reflects
open import Data.Nat.Path
open import Data.Fin.Inductive.Base
open import Data.List.Base
open import Data.List.Operations
  hiding (take ; lookup ; unzip ; all)

open import Data.Vec.Inductive.Base public

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  @0 n : ℕ

tabulate : {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = 0}     _ = []
tabulate {n = suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

take : (f : Fin (suc n)) → Vec A n → Vec A (fin→ℕ f)
take  fzero    _       = []
take (fsuc f) (x ∷ xs) = x ∷ take f xs

lookup : Vec A n → Fin n → A
lookup (x ∷ _)  fzero    = x
lookup (_ ∷ xs) (fsuc k) = lookup xs k

update : Fin n → (A → A) → Vec A n → Vec A n
update  fzero     f (x ∷ xs) = f x ∷ xs
update (fsuc idx) f (x ∷ xs) = x ∷ update idx f xs

replace : Fin n → A → Vec A n → Vec A n
replace f y = update f (λ _ → y)

vec→list : {A : Type ℓ} → Vec A n → Σ[ xs ꞉ List A ] Erased (length xs ＝ n)
vec→list [] = [] , erase refl
vec→list (x ∷ xs) =
  let xs′ , erase p = vec→list xs
  in x ∷ xs′ , erase (ap suc p)

list→vec : (xs : List A) → Σ[ len ꞉ ℕ ] Vec A len × (length xs ＝ len)
list→vec [] = 0 , [] , refl
list→vec (x ∷ xs) =
  let len′ , xs′ , p = list→vec xs
  in suc len′ , x ∷ xs′ , ap suc p

list→vec-n : (xs : List A) → Vec A (length xs)
list→vec-n []       = []
list→vec-n (x ∷ xs) = x ∷ list→vec-n xs

list-n→vec : (xs : List A) → {len : ℕ} → length xs ＝ len → Vec A len
list-n→vec []       {len = zero}  _   = []
list-n→vec []       {len = suc _} prf = false! prf
list-n→vec (x ∷ xs) {len = zero}  prf = false! prf
list-n→vec (x ∷ xs) {len = suc n} prf = x ∷ list-n→vec xs (suc-inj prf)

unzip : Vec (A × B) n → Vec A n × Vec B n
unzip []       = [] , []
unzip ((x , y) ∷ xys) =
  let (ihx , ihy) = unzip xys in
  x ∷ ihx , y ∷ ihy

all : (A → Bool) → Vec A n → Bool
all p []       = true
all p (x ∷ xs) = p x and all p xs

