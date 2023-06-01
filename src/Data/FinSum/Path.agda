{-# OPTIONS --safe #-}
module Data.FinSum.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Nat.Base
  using (ℕ; zero; suc)

open import Data.Fin.Base
  using ()
  renaming (Fin to Finⁱ; fzero to fzeroⁱ; fsuc to fsucⁱ)

open import Data.FinSum.Base

private variable n : ℕ

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
