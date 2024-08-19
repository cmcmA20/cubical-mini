{-# OPTIONS --safe #-}
module Data.Fin.Base where

open import Foundations.Base

open import Data.Empty.Base as ⊥
  using ()
open import Data.Fin.Interface
open import Data.Maybe.Base
  using (Maybe; nothing; just)
open import Data.Nat.Base
  using (ℕ; zero; suc)
open import Data.Sum.Base

private variable
  ℓ : Level
  m n : ℕ

Fin : ℕ → Type
Fin zero    = ⊥
Fin (suc n) = Maybe (Fin n)

pattern fzero  = nothing
pattern fsuc n = just n

fsplit : ∀[ n ꞉ ℕ ] Π[ k ꞉ Fin (suc n) ]
         (k ＝ fzero) ⊎ (Σ[ k′ ꞉ Fin n ] (k ＝ fsuc k′))
fsplit fzero    = inl refl
fsplit (fsuc k) = inr (k , refl)

elim
  : (P : ∀[ n ꞉ ℕ ] (Fin n → Type ℓ))
  → (∀[ n ꞉ ℕ ] P {suc n} fzero)
  → (∀[ n ꞉ ℕ ] ∀[ fn ꞉ Fin n ] (P fn → P (fsuc fn)))
  → ∀[ n ꞉ ℕ ] Π[ k ꞉ Fin n ] P k
elim P fz fs {suc n}  fzero    = fz
elim P fz fs {suc n}  (fsuc k) = fs (elim P fz fs k)

impl : FinI Fin
impl .FinI.fzero  = fzero
impl .FinI.fsuc   = fsuc
impl .FinI.fsplit = fsplit
impl .FinI.elim   = elim
