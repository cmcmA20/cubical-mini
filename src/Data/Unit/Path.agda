{-# OPTIONS --safe #-}
module Data.Unit.Path where

open import Foundations.Prelude

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Reflects.Base
open import Data.Unit.Base

⊤-path : (x y : ⊤) → (x ＝ y) ≃ ⊤
⊤-path _ _ .fst _ = tt
⊤-path x y .snd .equiv-proof = strict-contr-fibres (λ _ → reflₚ)

instance
  Reflects-⊤-Path : {x y : ⊤} → Reflects (x ＝ y) true
  Reflects-⊤-Path = ofʸ refl
  {-# OVERLAPPING Reflects-⊤-Path #-}

  ⊤-is-discrete : is-discrete ⊤
  ⊤-is-discrete = reflects-path→is-discrete!
