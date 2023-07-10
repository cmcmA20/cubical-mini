{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base
open import Foundations.Sigma

open import Meta.Search.HLevel

open import Structures.n-Type
open import Structures.FinSet

open import Correspondences.Decidable
open import Correspondences.Finite.Bishop

open import Data.Bool.Base public
open import Data.Dec.Base
open import Data.Bool.Instances.Finite
open import Data.Bool.Instances.Discrete

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

-- FinSet-Bool : FinSet 0ℓ
-- FinSet-Bool = fin-set! Bool

-- whew, painful
-- and-idem : ∀ x → x and x ＝ x
-- and-idem = witness (is-fin-set→exhaustible₁ {!!} {!!} )

-- and-idem = witness $
--   is-fin-set→exhaustible₁ (FinSet-Bool .FinSet.has-is-fin-set)
--     {P = λ x → el! (x and x ＝ x)} ?
--         {P = λ x → el! (x and x ＝ x)} (λ x → (x and x) ≟ x)

-- what : ∃[ b ꞉ Bool ] not b ＝ true
-- what = witness $
--   is-fin-set→omniscient₁ (FinSet-Bool .FinSet.has-is-fin-set)
--     {P = λ x → el! (not x ＝ true)} (λ x → not x ≟ true)

-- kek : Finite (Σ[ b ꞉ Bool ] not b ＝ b)
-- kek = {!!}

-- wow : ∃![ b ꞉ Bool ] not b ＝ b
-- wow = let t = fin-set! (Σ[ b ꞉ Bool ] not b ＝ b)
--   in {!!}

-- and-assoc : ∀ x y z → (x and y) and z ＝ x and (y and z)
-- and-assoc =
--   let t = is-fin-set→omniscient₁ (Bool-FinSet .FinSet.has-is-fin-set)
--   in {!!}
