{-# OPTIONS --safe #-}
module Meta.Projection where

open import Foundations.Base

open import Meta.Literals.FromProduct
  public
open import Meta.Reflection.Base
open import Meta.Reflection.Signature

open import Data.Bool.Base as Bool
open import Data.Empty.Base
open import Data.List.Base as List
open import Data.List.Base
  public
  using( [] ; _∷_ )
open import Data.List.Instances.FromProduct
  public
open import Data.Maybe.Base


private ⊤′ = ⊥ → ⊥

record Struct-proj-desc (stratified : Bool) (goal-projection : Name) : Type where
  field
    has-level : Name
    get-level : if stratified then (Term → TC Term) else ⊤′
    upwards-closure : if stratified then Name else ⊤′
    get-argument : List (Arg Term) → TC Term

open Struct-proj-desc

private
  work
    : {ℓ : Level} → Type ℓ → (stratified : Bool)
    → TC (List (Arg Term) × (Σ[ head ꞉ Name ] Struct-proj-desc stratified head))
  work A stratified = do
    def head args ← reduce =<< quoteTC A
      where ty → type-error [ "Goal is not a an application of a projection:" , termErr ty ]
    debug-print "tactic.search" 30
      [ "Trying projections for term:\n  " , termErr (def head args)
      , "\nwith head symbol ", nameErr head ]

    `stratified ← quoteTC stratified >>= normalise

    projection ← resetting do
      (mv , _) ← new-meta′ (it Struct-proj-desc ##ₙ `stratified ##ₙ lit (name head))
      get-instances mv >>= λ where
        (tm ∷ []) → unquoteTC {A = Struct-proj-desc stratified head} =<< normalise tm
        []        → type-error [ "Do not know how to invert projection\n  " , termErr (def head args) ]
        _         → type-error [ "Ambiguous inversions for projection\n  " , nameErr head ]

    returnTC $ args , head , projection


struct-proj : ∀ {ℓ} → Type ℓ → Maybe ℕ → Term → TC ⊤
struct-proj A nothing goal = do
  (args , head , projection) ← work A false

  x ← projection .get-argument args
  let soln = def (projection .has-level) [ argN x ]
  unify goal soln

struct-proj A (just want) goal = do
  want ← quoteTC want

  (args , head , projection) ← work A true

  x   ← projection .get-argument args
  lvl ← projection .get-level =<< infer-type x
  let soln = def (projection .upwards-closure)
        [ argN lvl , argN want
        , argN (it auto) , argN (def (projection .has-level) [ argN x ]) ]
  unify goal soln
