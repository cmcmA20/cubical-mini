{-# OPTIONS --guardedness #-}

module Cubical.IO.Finite where

open import Cubical.Data.Unit.Base
open import Agda.Builtin.String
open import Cubical.IO.Base
import Cubical.IO.Primitive as Prim
import Cubical.IO.Primitive.Finite as Prim
open import Cubical.Foundations.Prelude
open import Cubical.Interface.Show

open Show ⦃ ... ⦄

private
  variable
    ℓ ℓ′ : Level
    A : Type ℓ

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

getLine : IO String
getLine = lift Prim.getLine

-- Reads a finite file. Raises an exception if the file path refers to
-- a non-physical file (like "/dev/zero").

readFile : String → IO String
readFile f = lift (Prim.readFile f)

writeFile : String → String → IO {ℓ} Unit*
writeFile f s = lift′ (Prim.writeFile f s)

appendFile : String → String → IO {ℓ} Unit*
appendFile f s = lift′ (Prim.appendFile f s)

putStr : String → IO {ℓ} Unit*
putStr s = lift′ (Prim.putStr s)

putStrLn : String → IO {ℓ} Unit*
putStrLn s = lift′ (Prim.putStrLn s)

print : ⦃ Show A ⦄ → A → IO {ℓ′} Unit*
print a = putStr (show a)

printLn : ⦃ Show A ⦄ → A → IO {ℓ′} Unit*
printLn a = putStrLn (show a)
