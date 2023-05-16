{-# OPTIONS --guardedness #-}

module README where

------------------------------------------------------------------------
-- A programmer's library for Cubical Agda
-----------------------------------------------------------------------

-- The library comes with a .agda-lib file, for use with the library
-- management system.

------------------------------------------------------------------------
-- Module hierarchy
------------------------------------------------------------------------

-- Basic definitions, the toolset of a civilized man.
import Foundations.Everything

-- Automating boring things.
import Meta.Everything

-- Basic types and their properties.
import Data.Everything

-- n-truncations.
import Truncation.Everything

-- (Univalent) structures.
import Structures.Everything

-- Containers aka polynomial functors.
import Containers.Everything

-- I/O and related stuff.
import System.Everything

-- Modalities.
-- TODO import Modalities.Everything

-- TODO
-- -- Properties and proofs about relations
-- import Cubical.Relation.Everything
--
-- -- Category theory
-- import Cubical.Categories.Everything
--
-- -- Homotopy theory
-- import Cubical.Homotopy.Everything
--
-- -- Algebra library
-- import Cubical.Algebra.Everything
--
-- -- Cardinals
-- import Cubical.Cardinals.Everything
--
-- -- Displayed univalent graphs
-- import Cubical.Displayed.Everything
--
-- -- Homotopy level truncations
-- import Cubical.Truncations.Everything
--
-- -- Quotients
-- import Cubical.Quotients.Everything
