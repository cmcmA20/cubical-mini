{-# OPTIONS --safe #-}

-- The toolset of a civilized man.
module Prelude where

open import Foundations.Base          public
open import Foundations.Erased        public
open import Foundations.HLevel        public
open import Foundations.Path          public
open import Foundations.Pi            public
open import Foundations.Sigma         public
open import Foundations.Univalence    public

open import Structures.Instances.n-Type         public
open import Structures.Instances.IdentitySystem public
-- TODO add discrete and decidable stuff

open import Functions.Equiv.Biinv          public
open import Functions.Equiv.Fibrewise      public
open import Functions.Equiv.HalfAdjoint    public
open import Functions.Equiv.Weak           public
open import Functions.Embedding            public

-- FIXME change hierarchy
-- open import Truncation.Propositional.Base public

open import Containers.Base public

open import Meta.Everything public
