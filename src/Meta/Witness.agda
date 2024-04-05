{-# OPTIONS --safe #-}
module Meta.Witness where

open import Foundations.Base

open import Meta.Reflection.Base
open import Meta.Reflection.Signature
open import Meta.Reflection.Subst

open import Data.Dec.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.List.Instances.Idiom
open import Data.Reflects.Base

witness-macro : Term → TC ⊤
witness-macro hole = do
  ty ← (infer-type hole >>= reduce) >>= wait-just-a-bit
  debug-print "tactic.witness" 20 [ "Goal: " , termErr ty ]
  let supp = fv-ord ty
  ty′ ← generalize supp ty
  debug-print "tactic.witness" 20 [ "Generalized goal: " , termErr ty′ ]
  (mv , sol) ← new-meta′ $ it Dec ##ₕ unknown ##ₙ ty′
  (candidate ∷ []) ← get-instances mv where
    _ → type-error "No solutions or solution isn't unique"
  unify sol candidate
  let prf = it proof ##ₙ sol
      args = varg prf ∷ reverse-fast ((λ n → varg (var n [])) <$> supp)
  unify hole $ def (quote invert) args

macro witness! = witness-macro
