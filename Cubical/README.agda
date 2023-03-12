{-# OPTIONS --guardedness #-}

module Cubical.README where

------------------------------------------------------------------------
-- An experimental library for Cubical Agda
-----------------------------------------------------------------------

-- The library comes with a .agda-lib file, for use with the library
-- management system.

------------------------------------------------------------------------
-- Module hierarchy
------------------------------------------------------------------------

-- The core library for Cubical Agda.
-- It contains basic primitives, equivalences, glue types.
import Cubical.Core.Everything

-- The foundations for Cubical Agda.
-- The Prelude module is self-explanatory.
import Cubical.Foundations.Prelude
import Cubical.Foundations.Everything

-- Other modules (TODO: add descriptions)
import Cubical.Induction.Everything
import Cubical.Structures.Everything


import Cubical.Algebra.Everything

-- Reflection
import Cubical.Reflection.Everything

-- Displayed univalent graphs
import Cubical.Displayed.Everything


import Cubical.IO
