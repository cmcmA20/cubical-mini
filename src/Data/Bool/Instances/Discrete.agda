{-# OPTIONS --safe #-}
module Data.Bool.Instances.Discrete where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Decidability
open import Logic.Discreteness

open import Data.Dec.Base

open import Data.Bool.Base
open import Data.Bool.Path

private module BIS = IdSS (Extensional-Bool .idsᵉ) (hlevel 2)

==-reflects : Reflects (Path Bool) _==_
==-reflects m n with m == n | recall (m ==_) n
... | false | ⟪ p ⟫ = ofⁿ $ subst is-true p ∘ BIS.encode
... | true  | ⟪ p ⟫ = ofʸ $ BIS.decode $ subst is-true (sym p) tt

instance
  bool-is-discrete : is-discrete Bool
  bool-is-discrete { (false) } { (false) } = yes refl
  bool-is-discrete { (false) } { (true) }  = no false≠true
  bool-is-discrete { (true) }  { (false) } = no true≠false
  bool-is-discrete { (true) }  { (true) }  = yes refl
  {-# OVERLAPPING bool-is-discrete #-}
