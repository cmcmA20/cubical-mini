{-# OPTIONS --safe #-}
module Meta.Reflection.Solver where

open import Foundations.Base

open import Meta.Effect.Alt
open import Meta.Literals.FromString
open import Meta.Reflection.Base
open import Meta.Reflection.Variables

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Instances.FromProduct
open import Data.Maybe.Base
open import Data.Reflection.Error
open import Data.Reflection.Instances.FromString
open import Data.Reflection.Name
open import Data.Reflection.Term

private variable
  ℓ : Level
  A T : Type ℓ

--------------------------------------------------------------------------------
-- Helpers

solver-failed : Term → Term → TC A
solver-failed lhs rhs = type-error
  [ "Could not equate the following expressions:\n  "
  , term-err lhs , "\nAnd\n  " , term-err rhs ]

print-repr : Term → Term → TC A
print-repr tm repr = type-error
  [ "The expression\n  " , term-err tm
  , "\nIs represented by the expression\n  " , term-err repr ]

print-var-repr : Term → Term → Term → TC A
print-var-repr tm repr env = type-error
  [ "The expression\n  " , term-err tm
  , "\nIs represented by the expression\n  " , term-err repr
  , "\nIn the environment\n  " , term-err env ]

print-boundary : Term → TC A
print-boundary goal = type-error [ "Can't determine boundary: " , term-err goal ]


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

  withReduction : TC T → TC T
  withReduction = with-normalisation false
                ∘ with-reduce-defs (false , dont-reduce)

module _ (solver : Simple-solver) where
  open Simple-solver solver

  mk-simple-solver : Term → TC ⊤
  mk-simple-solver hole = withReduction do
    goal ← infer-type hole >>= reduce
    just (lhs , rhs) ← get-boundary goal where
      nothing → print-boundary goal
    lhs ← wait-just-a-bit lhs
    rhs ← wait-just-a-bit rhs
    elhs ← prepare lhs >>= build-expr
    erhs ← prepare rhs >>= build-expr
    no-constraints (unify hole $ invoke-solver elhs erhs)
      <|> solver-failed elhs erhs

  mk-simple-normalise : Term → Term → TC ⊤
  mk-simple-normalise tm hole = withReduction do
    e ← prepare tm >>= build-expr
    unify hole $ invoke-normaliser e

  mk-simple-repr : Term → Term → TC ⊤
  mk-simple-repr tm _ = withReduction do
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

  withReduction : TC T → TC T
  withReduction = with-normalisation false
                ∘ with-reduce-defs (false , dont-reduce)

module _ {ℓ} {A : Type ℓ} (solver : Variable-solver A) where
  open Variable-solver solver

  mk-var-solver : Term → TC ⊤
  mk-var-solver hole = withReduction do
    goal ← infer-type hole >>= reduce
    just (lhs , rhs) ← get-boundary goal
      where nothing → print-boundary goal
    lhs ← wait-just-a-bit lhs
    rhs ← wait-just-a-bit rhs
    elhs , vs ← prepare lhs >>= build-expr empty-vars
    debug-print "tactic.solver.var" 10 [ "LHS: " , term-err elhs ]
    erhs , vs ← prepare rhs >>= build-expr vs
    debug-print "tactic.solver.var" 10 [ "RHS: " , term-err erhs ]
    size , env ← environment vs
    debug-print "tactic.solver.var" 10 [ "Env: " , term-err env ]
    (no-constraints $ unify hole $ invoke-solver elhs erhs env) <|>
      solver-failed elhs erhs

  mk-var-normalise : Term → Term → TC ⊤
  mk-var-normalise tm hole = withReduction do
    e , vs ← prepare tm >>= build-expr empty-vars
    debug-print "tactic.solver.var" 10 [ "Expression: " , term-err e ]
    size , env ← environment vs
    debug-print "tactic.solver.var" 10 [ "Env: " , term-err env ]
    soln ← reduce $ invoke-normaliser e env
    unify hole soln

  mk-var-repr : Term → TC ⊤
  mk-var-repr tm = withReduction do
    repr , vs ← prepare tm >>= build-expr empty-vars
    size , env ← environment vs
    print-var-repr tm repr env
