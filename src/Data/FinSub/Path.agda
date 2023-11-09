{-# OPTIONS --safe #-}
module Data.FinSub.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Correspondences.Erased

open import Data.Nat.Base
  using (ℕ; zero; suc)
open import Data.Nat.Order.Computational

open import Data.Fin.Base
  using ()
  renaming (Fin to Finⁱ; fzero to fzeroⁱ; fsuc to fsucⁱ)

open import Data.FinSub.Base public

private variable n : ℕ

sub-fin→finⁱ : Fin n → Finⁱ n
sub-fin→finⁱ {suc n} (mk-fin 0            ) = fzeroⁱ
sub-fin→finⁱ {suc n} (mk-fin (suc k) {(b)}) = fsucⁱ $ sub-fin→finⁱ $ mk-fin k {b}

finⁱ→sub-fin : Finⁱ n → Fin n
finⁱ→sub-fin {suc _} fzeroⁱ    = fzero
finⁱ→sub-fin {suc _} (fsucⁱ k) = fsuc (finⁱ→sub-fin k)

sub-fin→finⁱ→sub-fin : (k : Fin n) → finⁱ→sub-fin {n} (sub-fin→finⁱ k) ＝ k
sub-fin→finⁱ→sub-fin {suc n} (mk-fin 0      ) = refl
sub-fin→finⁱ→sub-fin {suc n} (mk-fin (suc k)) = ap fsuc (sub-fin→finⁱ→sub-fin (mk-fin k))

finⁱ→sub-fin→finⁱ : (k : Finⁱ n) → sub-fin→finⁱ (finⁱ→sub-fin k) ＝ k
finⁱ→sub-fin→finⁱ {suc _} fzeroⁱ    = refl
finⁱ→sub-fin→finⁱ {suc _} (fsucⁱ k) = ap fsucⁱ $ finⁱ→sub-fin→finⁱ k

sub-fin≃finⁱ : Fin n ≃ Finⁱ n
sub-fin≃finⁱ = iso→equiv $ sub-fin→finⁱ ,
  iso finⁱ→sub-fin finⁱ→sub-fin→finⁱ sub-fin→finⁱ→sub-fin