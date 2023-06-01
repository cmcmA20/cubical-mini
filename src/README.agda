{-# OPTIONS --guarded #-}

module README where

------------------------------------------------------------------------
-- A programmer's library for Cubical Agda
-----------------------------------------------------------------------

-- Start here
import Prelude

------------------------------------------------------------------------
-- Module hierarchy
------------------------------------------------------------------------

-- Core definitions.
import Foundations.Everything

-- Basic types and their properties.
import Data.Everything

-- Function kinds.
import Functions.Everything

-- (Univalent) structures.
import Structures.Everything

-- Containers aka polynomial functors.
import Containers.Everything

-- Correspondences (proof-relevant relations).
import Correspondences.Everything

-- Homotopy level truncations.
import Truncation.Everything

-- Automating boring things.
import Meta.Everything

-- I/O and related stuff.
-- import System.Everything

-- Nullary correspondence is called a _structure_.
-- Prop-valued correspondence is called a _relation_.
-- Nullary relation/prop-valued structure is called a _property_.

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
