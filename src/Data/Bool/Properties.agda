{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Pi

open import Meta.Search.Decidable
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.Finite.Bishop
open import Meta.Search.Omniscient

open import Correspondences.Finite.Bishop
open import Correspondences.Finite.ManifestBishop

open import Data.Bool.Base public
open import Data.Bool.Instances.Finite
open import Data.Bool.Instances.Discrete
open import Data.Dec as Dec

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

instance
  and-idem? : Dec (∀ x → x and x ＝ x)
  and-idem? = Π-decision (λ x → (x and x) ≟ x) exhaust!

  and-comm? : Dec (∀ x y → x and y ＝ y and x)
  and-comm? = Π-decision (λ x → Π-decision (λ y → (x and y) ≟ (y and x)) exhaust!) exhaust!

  test? : Dec (∃[ f ꞉ (Bool → Bool) ] f false ＝ f true)
  test? = ∃-decision (λ f → f false ≟ f true) (is-fin-set→omniscient₁ (fun-is-fin-set bool-is-fin-set bool-is-fin-set))

opaque
  unfolding
    is-discrete-β is-fin-set-β omniscient₁-β exhaustible-β omniscient₁→exhaustible
    𝓑 is-fin-set→omniscient₁ 𝓑→omniscient₁ ∥-∥₁.rec

  -- unfolding
  --  _∙ₑ_ is-equiv-comp cardinality enumeration

  and-idem : ∀ x → x and x ＝ x
  and-idem = witness!

  and-comm : ∀ x y → x and y ＝ y and x
  and-comm = witness!
