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

-- conjunction

and-idem : (x : Bool) → x and x ＝ x
and-idem = witness!

and-comm : ∀ x y → x and y ＝ y and x
and-comm = witness!


-- negation

not-invol : ∀ x → not (not x) ＝ x
not-invol = witness!

≠→=not : ∀ x y → x ≠ y → x ＝ not y
≠→=not = witness!


-- disjunction

or-id-r : ∀ x → x or false ＝ x
or-id-r = witness!

or-absorb-r : ∀ x → x or true ＝ true
or-absorb-r = witness!

or-assoc : ∀ x y z → (x or y) or z ＝ x or y or z
or-assoc = witness!

or-comm : ∀ x y → x or y ＝ y or x
or-comm = witness!

or-idem : ∀ x → x or x ＝ x
or-idem = witness!
