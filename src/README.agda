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

-- Function kinds.
import Functions.Everything

-- Homotopy level truncations.
import Truncation.Everything

-- (Univalent) structures.
import Structures.Everything

-- Containers aka polynomial functors.
import Containers.Everything

-- I/O and related stuff.
import System.Everything

-- Relations and their properties.
-- Note that nullary relations are actually `Structures`.
-- TODO import Relations.Everything

-- Modalities.
-- TODO import Modalities.Everything

-- TODO
-- -- Category theory
-- import Cubical.Categories.Everything
--
-- -- Quotients
-- import Cubical.Quotients.Everything
--
-- -- Homotopy theory
-- import Cubical.Homotopy.Everything
--
-- -- Algebra library
-- import Cubical.Algebra.Everything
--
-- -- Cardinals
-- import Cubical.Cardinals.Everything
