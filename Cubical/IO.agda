{-# OPTIONS --guardedness #-}

module Cubical.IO where

open import Agda.Builtin.Coinduction
-- open import Codata.Musical.Costring
open import Cubical.Data.Unit.Base
open import Cubical.Data.String.Base
-- import Data.Unit.Base as Unit0
open import Cubical.Foundations.Function
import Cubical.IO.Primitive as Prim
open import Cubical.Foundations.Prelude

private
  variable
    ℓᵃ ℓᵇ : Level
    A : Type ℓᵃ
    B : Type ℓᵇ

------------------------------------------------------------------------
-- Re-exporting the basic type and functions

open import Cubical.IO.Base public

------------------------------------------------------------------------
-- Utilities

module List where

  open import Cubical.Data.List.Base

  sequence : List (IO A) → IO (List A)
  sequence []       = ⦇ [] ⦈
  sequence (c ∷ cs) = ⦇ c ∷ sequence cs ⦈

  -- The reason for not defining sequence′ in terms of sequence is
  -- efficiency (the unused results could cause unnecessary memory use).

  sequence′ : List (IO A) → IO Unit*
  sequence′ []       = pure _
  sequence′ (c ∷ cs) = c >> sequence′ cs

  mapM : (A → IO B) → List A → IO (List B)
  mapM f = sequence ∘ map f

  mapM′ : (A → IO B) → List A → IO Unit*
  mapM′ f = sequence′ ∘ map f

  forM : List A → (A → IO B) → IO (List B)
  forM = flip mapM

  forM′ : List A → (A → IO B) → IO Unit*
  forM′ = flip mapM′

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

open import Cubical.IO.Finite public
  renaming (readFile to readFiniteFile)

-- open import IO.Infinite public
--   renaming ( writeFile  to writeFile∞
--            ; appendFile to appendFile∞
--            ; putStr     to putStr∞
--            ; putStrLn   to putStrLn∞
--            )
