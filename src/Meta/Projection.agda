{-# OPTIONS --safe --no-exact-split #-}
module Meta.Projection where

open import Foundations.Base

open import Meta.Effect.Bind
open import Meta.Literals.FromProduct
  public
open import Meta.Reflection

open import Data.Bool.Base as Bool
open import Data.Empty.Base
open import Data.List.Base as List
open import Data.List.Base
  public
  using( [] ; _∷_ )
open import Data.List.Instances.FromProduct
  public
open import Data.Maybe.Base
open import Data.Nat.Instances.FromNat
open import Data.Reflection.Abs
open import Data.Reflection.Argument
open import Data.Reflection.Error
open import Data.Reflection.Fixity
open import Data.Reflection.Instances.FromString
open import Data.Reflection.Literal
open import Data.Reflection.Meta
open import Data.Reflection.Name
open import Data.Reflection.Term
open import Data.Unit.Base

open Bind ⦃ ... ⦄

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
      where ty → type-error [ "Goal is not a an application of a projection:" , term-err ty ]
    debug-print "tactic.search" 30
      [ "Trying projections for term:\n  " , term-err (def head args)
      , "\nwith head symbol ", name-err head ]

    `stratified ← quoteTC stratified >>= normalise

    projection ← resetting do
      (mv , _) ← new-meta′ (it Struct-proj-desc ##ₙ `stratified ##ₙ lit (name head))
      get-instances mv >>= λ where
        (tm ∷ []) → unquoteTC {A = Struct-proj-desc stratified head} =<< normalise tm
        []        → type-error [ "Do not know how to invert projection\n  " , term-err (def head args) ]
        _         → type-error [ "Ambiguous inversions for projection\n  " , name-err head ]

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
