{-# OPTIONS --safe #-}
-- The toolset of a civilized man.
module Prelude where

open import Meta.Prelude public

open import Meta.Literals.FromProduct public
open import Meta.Literals.FromNat     public
open import Meta.Literals.FromNeg     public
open import Meta.Literals.FromString  public
open import Meta.Notation.Membership  public
open import Meta.Show                 public
open import Meta.Witness              public

open import Meta.Deriving.HLevel public
open import Meta.Deriving.Show   public
open import Meta.Extensionality  public
open import Meta.Marker          public
open import Meta.Record          public
open import Meta.SIP             public

open import Structures.n-Type public

open import Logic.Decidability   public
open import Logic.Discreteness   public
open import Logic.Exhaustibility public
open import Logic.Omniscience    public

open import Combinatorics.Finiteness.Bishop.Weak     public
open import Combinatorics.Finiteness.Bishop.Manifest public

open import Functions.Equiv.Weak public
open import Functions.Embedding  public
open import Functions.Fibration  public
open import Functions.Surjection public

import Data.Truncation.Propositional
module ∥-∥₁ = Data.Truncation.Propositional
open ∥-∥₁ public
  using ( ∥_∥₁ ; ∣_∣₁ ; squash₁
        ; ∃ ; ∃-syntax-und ; ∃[_]
        ; _⊎₁_ ; _⊎̇₁_
        ; fibre₁ ; Im )

import Data.Truncation.Set
module ∥-∥₂ = Data.Truncation.Set
open ∥-∥₂ public
  using ( ∥_∥₂ ; ∣_∣₂ ; squash₂ )
