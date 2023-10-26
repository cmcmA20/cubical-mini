{-# OPTIONS --safe #-}
module Meta.Witness where

open import Foundations.Base

open import Meta.Reflection
open import Meta.Search.Decidable

open import Correspondences.Discrete
open import Correspondences.Finite.Bishop
open import Correspondences.Finite.ManifestBishop
open import Correspondences.Omniscient

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.FinSub.Closure
open import Data.FinSub.Properties
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Vec.Correspondences.Unary.Any.Computational

witness-macro : Bool → Term → TC ⊤
witness-macro _ (lam _ _) = commitTC -- Agda's too smart about unit type
witness-macro strict? hole = do
  ty ← inferType hole >>= reduce
  candidate ← new-meta (def (quote Dec) (unknown h∷ ty v∷ []))
  decide-tactic-worker candidate
  let prf = def (quote proof) (candidate v∷ [])
  true ← pure strict? where
    false → do
      solution ← reduce $ def (quote Reflects′.invert) (prf v∷ [])
      unify hole solution
  con (quote ofʸ) (_ ∷ _ ∷ solution v∷ []) ← reduce $ prf
    where x → typeError [ "Goal is actually false (" , termErr x , ")" ]
  unify hole solution

macro witness! = witness-macro false
macro witness-strict! = witness-macro true

opaque
  unfolding
    is-discrete-β omniscient₁→exhaustible is-fin-set→omniscient₁ 𝓑→omniscient₁

    -- yes it's a kludge
  witness-opaque-marker : ⊤
  witness-opaque-marker = tt
