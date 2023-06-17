{-# OPTIONS --safe #-}
module Data.FinSum.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Nat.Base
  using (ℕ; zero; suc)

open import Data.Fin.Base
  using ()
  renaming (Fin to Finⁱ; fzero to fzeroⁱ; fsuc to fsucⁱ)

open import Data.FinSum.Base public

private variable n : ℕ

sum-fin→finⁱ : Fin n → Finⁱ n
sum-fin→finⁱ {suc _} fzero    = fzeroⁱ
sum-fin→finⁱ {suc _} (fsuc k) = fsucⁱ (sum-fin→finⁱ k)

finⁱ→sum-fin : Finⁱ n → Fin n
finⁱ→sum-fin {suc _} fzeroⁱ    = fzero
finⁱ→sum-fin {suc _} (fsucⁱ k) = fsuc (finⁱ→sum-fin k)

sum-fin→finⁱ→sum-fin : (k : Fin n) → finⁱ→sum-fin (sum-fin→finⁱ k) ＝ k
sum-fin→finⁱ→sum-fin {suc _} fzero    = refl
sum-fin→finⁱ→sum-fin {suc _} (fsuc k) = ap fsuc (sum-fin→finⁱ→sum-fin k)

finⁱ→sum-fin→finⁱ : (k : Finⁱ n) → sum-fin→finⁱ (finⁱ→sum-fin k) ＝ k
finⁱ→sum-fin→finⁱ {suc _} fzeroⁱ    = refl
finⁱ→sum-fin→finⁱ {suc _} (fsucⁱ k) = ap fsucⁱ (finⁱ→sum-fin→finⁱ k)

sum-fin≃finⁱ : Fin n ≃ Finⁱ n
sum-fin≃finⁱ = iso→equiv $ sum-fin→finⁱ ,
  iso finⁱ→sum-fin finⁱ→sum-fin→finⁱ sum-fin→finⁱ→sum-fin
