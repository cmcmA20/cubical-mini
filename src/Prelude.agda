{-# OPTIONS --safe #-}
-- The toolset of a civilized man.
module Prelude where

open import Meta.Prelude public

open import Meta.Effect.Alt         public
open import Meta.Effect.Bind        public
open import Meta.Effect.Foldable    public
open import Meta.Effect.Idiom       public
open import Meta.Effect.Map         public
open import Meta.Effect.Traversable public

open import Meta.Append               public
open import Meta.Literals.FromProduct public
open import Meta.Literals.FromNat     public
open import Meta.Literals.FromNeg     public
open import Meta.Literals.FromString  public
open import Meta.Membership           public
open import Meta.Ord                  public
open import Meta.Show                 public

open import Structures.n-Type public

open import Correspondences.Decidable             public
open import Correspondences.Discrete              public
open import Correspondences.Exhaustible           public
open import Correspondences.Finite.Bishop         public
open import Correspondences.Finite.ManifestBishop public
open import Correspondences.Omniscient            public

open import Meta.Deriving.HLevel public
open import Meta.Deriving.Show   public
open import Meta.Extensionality  public
open import Meta.Marker          public
open import Meta.Record          public
open import Meta.SIP             public

open import Functions.Equiv.Fibrewise public
open import Functions.Equiv.Weak      public
open import Functions.Embedding       public
open import Functions.Fibration       public

import Truncation.Propositional
module ∥-∥₁ = Truncation.Propositional
open ∥-∥₁ public
  using ( ∥_∥₁ ; ∣_∣₁ ; squash₁
        ; ∃ ; ∃-syntax-und ; ∃[_]
        ; _⊎₁_ ; _⊎̇₁_
        ; fibre₁ ; Im )

import Truncation.Set
module ∥-∥₂ = Truncation.Set
open ∥-∥₂ public
  using ( ∥_∥₂ ; ∣_∣₂ ; squash₂ )
