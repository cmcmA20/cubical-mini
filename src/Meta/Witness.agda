{-# OPTIONS --safe #-}
-- -vtactic.witness:20
module Meta.Witness where

open import Foundations.Base

open import Meta.Reflection
open import Meta.Search.Decidable
open import Meta.Subst

open import Data.Dec.Base
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Idiom

witness-macro : Term → TC ⊤
witness-macro (lam _ _) = commitTC -- Agda's too smart about unit type
witness-macro hole = do
  ty ← (inferType hole >>= reduce) >>= wait-just-a-bit
  debugPrint "tactic.witness" 20 [ "Goal: " , termErr ty ]
  let supp = fv-ord ty
  ty′ ← generalize supp ty
  debugPrint "tactic.witness" 20 [ "Generalized goal: " , termErr ty′ ]
  candidate ← new-meta (def (quote Dec) (unknown h∷ ty′ v∷ []))
  decide-tactic-worker candidate
  let prf  = def (quote proof) (candidate v∷ [])
      args = varg prf ∷ reverse-fast ((λ n → varg (var n [])) <$> supp)
  unify hole (def (quote Reflects′.invert) args)

macro witness! = witness-macro
