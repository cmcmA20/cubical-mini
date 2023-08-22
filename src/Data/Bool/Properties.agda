{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base

open import Meta.Search.Decidable
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.Finite.Bishop
open import Meta.Search.Omniscient
open import Meta.Witness

open import Data.Bool.Base public
open import Data.Bool.Instances.Finite
open import Data.Dec as Dec

import Truncation.Propositional as ∥-∥₁
open ∥-∥₁

private
  instance
    and-idem? : Dec $ ∀ x → x and x ＝ x
    and-idem? = decide!

    and-comm? : Dec $ ∀ x y → x and y ＝ y and x
    and-comm? = decide!

    test? : Dec $ ∃[ f ꞉ (Bool → Bool) ] f false ＝ f true
    test? = decide!

    test₂? : Dec (((x , y) : Bool × Bool) → x and y ＝ y and x)
    test₂? = decide!

    -- test₃? : Dec $
    --   ∃[ f ꞉ (Bool → Bool → Bool) ]
    --   ∃[ g ꞉ (Bool → Bool) ]
    --   Π[ h ꞉ (Bool → Bool) ]
    --     (f false true ＝ g true and h false)
    -- test₃? = decide!

  opaque
    unfolding witness-opaque-marker bool-is-fin-set

    and-idem : (x : Bool) → x and x ＝ x
    and-idem = witness!

    and-comm : ∀ x y → x and y ＝ y and x
    and-comm = witness!

    test : ∃[ f ꞉ (Bool → Bool) ] f false ＝ f true
    test = witness!

    test₂ : ((x , y) : Bool × Bool) → x and y ＝ y and x
    test₂ = witness!

    -- slow, uncomment if needed
    -- test₃ :
    --   ∃[ f ꞉ (Bool → Bool → Bool) ]
    --   ∃[ g ꞉ (Bool → Bool) ]
    --   Π[ h ꞉ (Bool → Bool) ]
    --     (f false true ＝ g true and h false)
    -- test₃ = witness!

-- boolean disjunction

or-id-r : ∀ x → x or false ＝ x
or-id-r false = refl
or-id-r true  = refl

or-unit-r : ∀ x → x or true ＝ true
or-unit-r false = refl
or-unit-r true  = refl

or-assoc : ∀ x y z → (x or y) or z ＝ x or y or z
or-assoc false y z = refl
or-assoc true  y z = refl

or-comm : ∀ x y → x or y ＝ y or x
or-comm x false = or-id-r x
or-comm x true  = or-unit-r x

or-idem : ∀ x → x or x ＝ x
or-idem false = refl
or-idem true  = refl