{-# OPTIONS --safe #-}
module Meta.Solver where

open import Foundations.Base

open import Meta.Literals.FromString
open import Meta.Variables
open import Meta.Reflection

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Maybe.Base

private variable
  ℓ : Level
  A : Type ℓ

--------------------------------------------------------------------------------
-- Helpers

solver-failed : Term → Term → TC A
solver-failed lhs rhs = typeError
  [ "Could not equate the following expressions:\n  "
  , termErr lhs , "\nAnd\n  " , termErr rhs ]

print-repr : Term → Term → TC A
print-repr tm repr = typeError
  [ "The expression\n  " , termErr tm
  , "\nIs represented by the expression\n  " , termErr repr ]

print-var-repr : Term → Term → Term → TC A
print-var-repr tm repr env = typeError
  [ "The expression\n  " , termErr tm
  , "\nIs represented by the expression\n  " , termErr repr
  , "\nIn the environment\n  " , termErr env ]

print-boundary : Term → TC A
print-boundary goal = typeError [ "Can't determine boundary: " , termErr goal ]


data Reduction-strategy : Type where
  no whnf norm : Reduction-strategy

private
  prepare′ : Reduction-strategy → Term → TC Term
  prepare′ no   = pure
  prepare′ whnf = reduce
  prepare′ norm = normalise


--------------------------------------------------------------------------------
-- Simple Solvers

record Simple-solver : Type where
  constructor simple-solver
  field
    dont-reduce       : List Name
    build-expr        : Term → TC Term
    strat             : Reduction-strategy
    invoke-solver     : Term → Term → Term
    invoke-normaliser : Term → Term

  prepare = prepare′ strat

module _ (solver : Simple-solver) where
  open Simple-solver solver

  mk-simple-solver : Term → TC ⊤
  mk-simple-solver hole = withNormalisation false $ withReduceDefs (false , dont-reduce) do
      goal ← inferType hole >>= reduce
      just (lhs , rhs) ← get-boundary goal where
        nothing → print-boundary goal
      elhs ← prepare lhs >>= build-expr
      erhs ← prepare rhs >>= build-expr
      noConstraints (unify hole $ invoke-solver elhs erhs)
        <|> solver-failed elhs erhs

  mk-simple-normalise : Term → Term → TC ⊤
  mk-simple-normalise tm hole = withNormalisation false $ withReduceDefs (false , dont-reduce) do
      e ← prepare tm >>= build-expr
      unify hole $ invoke-normaliser e

  mk-simple-repr : Term → Term → TC ⊤
  mk-simple-repr tm _ = withNormalisation false $ withReduceDefs (false , dont-reduce) do
      repr ← prepare tm >>= build-expr
      print-repr tm repr


--------------------------------------------------------------------------------
-- Solvers with Variables

record Variable-solver {ℓ} (A : Type ℓ) : Type ℓ where
  constructor var-solver
  field
    dont-reduce       : List Name
    build-expr        : Variables A → Term → TC (Term × Variables A)
    strat             : Reduction-strategy
    invoke-solver     : Term → Term → Term → Term
    invoke-normaliser : Term → Term → Term

  prepare = prepare′ strat

module _ {ℓ} {A : Type ℓ} (solver : Variable-solver A) where
  open Variable-solver solver

  mk-var-solver : Term → TC ⊤
  mk-var-solver hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    goal ← inferType hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → print-boundary goal
    elhs , vs ← prepare lhs >>= build-expr empty-vars
    erhs , vs ← prepare rhs >>= build-expr vs
    size , env ← environment vs
    (noConstraints $ unify hole $ invoke-solver elhs erhs env) <|>
      solver-failed elhs erhs

  mk-var-normalise : Term → Term → TC ⊤
  mk-var-normalise tm hole =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    e , vs ← prepare tm >>= build-expr empty-vars
    size , env ← environment vs
    soln ← reduce $ invoke-normaliser e env
    unify hole soln

  mk-var-repr : Term → TC ⊤
  mk-var-repr tm =
    withNormalisation false $
    withReduceDefs (false , dont-reduce) $ do
    repr , vs ← prepare tm >>= build-expr empty-vars
    size , env ← environment vs
    print-var-repr tm repr env
