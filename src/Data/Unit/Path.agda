{-# OPTIONS --safe #-}
module Data.Unit.Path where

open import Foundations.Base

open import Data.Unit.Base public

⊤-is-contr : is-contr ⊤
⊤-is-contr .fst = tt
⊤-is-contr .snd tt = refl
