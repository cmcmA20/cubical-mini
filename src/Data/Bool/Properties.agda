{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base

open import Meta.Search.Decidable
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.Finite.Bishop
open import Meta.Search.Omniscient
open import Meta.Witness

open import Data.Empty.Base
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

-- negation

not-invol : ∀ x → not (not x) ＝ x
not-invol true  = refl
not-invol false = refl

≠→=not : ∀ x y → x ≠ y → x ＝ not y
≠→=not false false p = absurd (p refl)
≠→=not false true  _ = refl
≠→=not true  false _ = refl
≠→=not true  true  p = absurd (p refl)

-- disjunction

or-id-r : ∀ x → x or false ＝ x
or-id-r false = refl
or-id-r true  = refl

or-absorb-r : ∀ x → x or true ＝ true
or-absorb-r false = refl
or-absorb-r true  = refl

or-assoc : ∀ x y z → (x or y) or z ＝ x or y or z
or-assoc false _ _ = refl
or-assoc true  _ _ = refl

or-comm : ∀ x y → x or y ＝ y or x
or-comm x false = or-id-r x
or-comm x true  = or-absorb-r x

or-idem : ∀ x → x or x ＝ x
or-idem false = refl
or-idem true  = refl
