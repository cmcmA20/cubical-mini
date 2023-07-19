{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base

open import Meta.Search.Decidable
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.Finite.Bishop
open import Meta.Search.Omniscient

open import Correspondences.Finite.ManifestBishop

open import Data.Bool.Base public
open import Data.Bool.Instances.Finite
open import Data.Dec as Dec
open import Data.FinSub.Properties
open import Data.FinSub.Closure
open import Data.Vec.Correspondences.Unary.Any.Computational

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

instance
  and-idem? : Dec (∀ x → x and x ＝ x)
  and-idem? = decide!

  and-comm? : Dec (∀ x y → x and y ＝ y and x)
  and-comm? = decide!

  test? : Dec (∃[ f ꞉ (Bool → Bool) ] f false ＝ f true)
  test? = decide!

  test₂? : Dec (((x , y) : Bool × Bool) → x and y ＝ y and x)
  test₂? = decide!

opaque
  unfolding
    is-discrete-β is-fin-set-β omniscient₁-β exhaustible-β omniscient₁→exhaustible
    𝓑 is-fin-set→omniscient₁ 𝓑→omniscient₁ bool-is-fin-set any? finite-pi-fin
    fin-sum fin-suc-universal fin-choice

  and-idem : (x : Bool) → x and x ＝ x
  and-idem = witness!

  and-comm : ∀ x y → x and y ＝ y and x
  and-comm = witness!

  test : ∃[ f ꞉ (Bool → Bool) ] f false ＝ f true
  test = witness!

  test₂ : ((x , y) : Bool × Bool) → x and y ＝ y and x
  test₂ = witness!
