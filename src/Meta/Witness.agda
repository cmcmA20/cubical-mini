{-# OPTIONS --safe #-}
-- -vtactic.witness:20
module Meta.Witness where

open import Foundations.Base

open import Meta.Reflection
open import Meta.Search.Decidable

open import Data.Dec.Base
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Idiom

-- TODO do not generalize over unused variables
witness-macro : Term → TC ⊤
witness-macro (lam _ _) = commitTC -- Agda's too smart about unit type
witness-macro hole = do
  ty ← (inferType hole >>= reduce) >>= wait-just-a-bit
  debugPrint "tactic.witness" 20 [ "Goal type: " , termErr ty ]
  ctx ← getContext
  let ty′ = generalize ctx ty
  debugPrint "tactic.witness" 20 [ "Generalized: " , termErr ty′ ]
  candidate ← new-meta (def (quote Dec) (unknown h∷ ty′ v∷ []))
  decide-tactic-worker candidate
  let prf  = def (quote proof) (candidate v∷ [])
      args = varg prf ∷ reverse-fast (instantiated-args ctx)
  unify hole (def (quote Reflects′.invert) args)

macro witness! = witness-macro
