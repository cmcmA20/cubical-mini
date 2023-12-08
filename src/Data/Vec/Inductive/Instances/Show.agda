{-# OPTIONS --safe #-}
module Data.Vec.Inductive.Instances.Show where

open import Foundations.Base

open import Meta.Deriving.Show

open import Data.Vec.Inductive.Base

-- TODO erased modality
-- instance
--   unquoteDecl Show-Vec = derive-show Show-Vec (quote Vec)

-- private module _ where
--   open import Data.Nat.Instances.Show

--   _ : show (1 ∷ 2 ∷ 3 ∷ []) ＝ "1 ∷ 2 ∷ 3 ∷ []"
--   _ = refl

--   _ : show ((1 ∷ []) ∷ (2 ∷ []) ∷ []) ＝ "(1 ∷ []) ∷ (2 ∷ []) ∷ []"
--   _ = refl
