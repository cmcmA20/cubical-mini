{-# OPTIONS --safe #-}
module Data.Unit.Path where

open import Foundations.Base
open import Foundations.Equiv.Base

open import Data.Unit.Base

⊤-path : (x y : ⊤) → (x ＝ y) ≃ ⊤
⊤-path _ _ .fst _ = tt
⊤-path x y .snd .equiv-proof = strict-contr-fibres (λ _ → refl)
