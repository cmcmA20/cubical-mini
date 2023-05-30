{-# OPTIONS --safe #-}
module Data.Fin.Sum where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Nat.Base
  using (ℕ; zero; suc)
open import Data.Empty.Base
  using (⊥; absurd)
open import Data.Sum.Base

open import Data.Fin.Base
  using ()
  renaming (Fin to Finⁱ; fzero to fzeroⁱ; fsuc to fsucⁱ )
import      Data.Fin.Base as Finⁱ

private variable
  ℓ : Level
  m n : ℕ

Fin : ℕ → Type
Fin zero    = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

pattern fzero  = inl tt
pattern fsuc n = inr n

elim
  : (P : ∀ {n} → Fin n → Type ℓ)
  → (∀ {n} → P {suc n} fzero)
  → (∀ {n} {fn : Fin n} → P fn → P (fsuc fn))
  → {n : ℕ} (fn : Fin n) → P fn
elim P fz fs {(zero)} f0        = absurd f0
elim P fz fs {suc k}  fzero     = fz
elim P fz fs {suc k}  (fsuc fk) = fs (elim P fz fs fk)

sum-fin→finⁱ : Fin n → Finⁱ n
sum-fin→finⁱ {suc n} fzero    = fzeroⁱ
sum-fin→finⁱ {suc n} (fsuc k) = fsucⁱ (sum-fin→finⁱ k)

finⁱ→sum-fin : Finⁱ n → Fin n
finⁱ→sum-fin fzeroⁱ    = fzero
finⁱ→sum-fin (fsucⁱ k) = fsuc (finⁱ→sum-fin k)

sum-fin→finⁱ→sum-fin : (k : Fin n) → finⁱ→sum-fin (sum-fin→finⁱ k) ＝ k
sum-fin→finⁱ→sum-fin {suc n} fzero    = refl
sum-fin→finⁱ→sum-fin {suc n} (fsuc k) = ap fsuc (sum-fin→finⁱ→sum-fin k)

finⁱ→sum-fin→finⁱ : (k : Finⁱ n) → sum-fin→finⁱ (finⁱ→sum-fin k) ＝ k
finⁱ→sum-fin→finⁱ fzeroⁱ    = refl
finⁱ→sum-fin→finⁱ (fsucⁱ k) = ap fsucⁱ (finⁱ→sum-fin→finⁱ k)

sum-fin≃finⁱ : Fin n ≃ Finⁱ n
sum-fin≃finⁱ =
  iso→equiv (sum-fin→finⁱ , iso finⁱ→sum-fin finⁱ→sum-fin→finⁱ sum-fin→finⁱ→sum-fin)
