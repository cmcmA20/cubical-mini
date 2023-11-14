{-# OPTIONS --safe #-}
-- The toolset of a civilized man.
module Prelude where

open import Foundations.Base       public
open import Foundations.Path       public
open import Foundations.Pi         public
open import Foundations.Sigma      public
open import Foundations.Transport  public
open import Foundations.Univalence public

open import Meta.Alt      public
open import Meta.Bind     public
open import Meta.Foldable public
open import Meta.Idiom    public
open import Meta.Traverse public

open import Meta.Literals.FromProduct public
open import Meta.Literals.FromNat     public
open import Meta.Literals.FromNeg     public
open import Meta.Literals.FromString  public
open import Meta.Show                 public

open import Meta.Search.Decidable     public
open import Meta.Search.Discrete      public
open import Meta.Search.Exhaustible   public
open import Meta.Search.Finite.Bishop public
open import Meta.Search.HLevel        public
open import Meta.Search.Omniscient    public

open import Meta.Marker     public
open import Meta.Record     public
open import Meta.SIP        public
open import Meta.Underlying public

open import Structures.n-Type public

open import Correspondences.Erased public

open import Functions.Equiv.Fibrewise public
open import Functions.Equiv.Weak      public
open import Functions.Embedding       public
open import Functions.Fibration       public

import Truncation.Propositional
module ∥-∥₁ = Truncation.Propositional
open ∥-∥₁ public
  using (∥_∥₁; ∣_∣₁; squash₁; ∃; ∃-syntax; _⊎₁_; Im)

import Truncation.Set
module ∥-∥₂ = Truncation.Set
open ∥-∥₂ public
  using (∥_∥₂; ∣_∣₂; squash₂)
