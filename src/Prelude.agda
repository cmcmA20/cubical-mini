{-# OPTIONS --safe #-}
-- The toolset of a civilized man.
module Prelude where

open import Foundations.Base       public
open import Foundations.Erased     public
open import Foundations.HLevel     public
open import Foundations.Path       public
open import Foundations.Pi         public
open import Foundations.Sigma      public
open import Foundations.Univalence public

open import Structures.n-Type public

open import Functions.Equiv.Fibrewise public
open import Functions.Equiv.Weak      public
open import Functions.Embedding       public

import Truncation.Propositional
module ∥-∥₁ = Truncation.Propositional
open ∥-∥₁ public
  using (∥_∥₁; ∣_∣₁; squash₁; ∃; ∃-syntax; image)


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

open import Meta.Finite   public
open import Meta.HLevel   public

open import Meta.Marker     public
open import Meta.Record     public
open import Meta.SIP        public
open import Meta.Underlying public
