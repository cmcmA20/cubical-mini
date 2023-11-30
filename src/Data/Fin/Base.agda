{-# OPTIONS --safe #-}
module Data.Fin.Base where

open import Foundations.Base

open import Data.Empty.Base as ⊥
  using (⊥)
open import Data.Fin.Interface
open import Data.Maybe.Base
  using (Maybe; nothing; just)
open import Data.Nat.Base
  using (ℕ; zero; suc)

private variable
  ℓ : Level
  m n : ℕ

Fin : ℕ → Type
Fin zero    = ⊥
Fin (suc n) = Maybe (Fin n)

pattern fzero  = nothing
pattern fsuc n = just n

elim
  : (P : ∀ᴱ[ n ꞉ ℕ ] (Fin n → Type ℓ))
  → (∀ᴱ[ n ꞉ ℕ ] P {suc n} fzero)
  → (∀ᴱ[ n ꞉ ℕ ] ∀[ fn ꞉ Fin n ] (P fn → P (fsuc fn)))
  → ∀[ n ꞉ ℕ ] Π[ k ꞉ Fin n ] P k
elim P fz fs {(zero)} f0       = ⊥.rec f0
elim P fz fs {suc n}  fzero    = fz
elim P fz fs {suc n}  (fsuc k) = fs (elim P fz fs k)

fpred : Fin (suc (suc n)) → Fin (suc n)
fpred fzero    = fzero
fpred (fsuc k) = k

impl : FinI (λ n → Fin n)
impl .FinI.fzero = fzero
impl .FinI.fsuc  = fsuc
impl .FinI.elim  = elim
impl .FinI.fpred = fpred
