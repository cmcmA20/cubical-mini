{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.Decidable
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.Finite.Bishop
open import Meta.Search.Finite.ManifestBishop
open import Meta.Search.Omniscient
open import Meta.Witness

open import Data.Empty.Base
open import Data.Bool.Base as Bool public
open import Data.Bool.Instances.Finite

private variable
  ℓᵃ : Level
  A : Type ℓᵃ

universal : (Bool → A)
          ≃ A × A
universal = iso→equiv
  $ (λ ch → ch true , ch false)
  , iso (flip (Bool.rec fst snd))
        (λ _ → refl)
        (λ _ → fun-ext $ Bool.elim refl refl)


-- conjunction

and-id-r : ∀ x → x and true ＝ x
and-id-r = witness!

and-absorb-r : ∀ x → x and false ＝ false
and-absorb-r = witness!

and-assoc : ∀ x y z → (x and y) and z ＝ x and y and z
and-assoc = witness!

and-idem : ∀ x → x and x ＝ x
and-idem = witness!

and-comm : ∀ x y → x and y ＝ y and x
and-comm = witness!

and-compl : ∀ x → x and not x ＝ false
and-compl = witness!

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

or-compl : ∀ x → x or not x ＝ true
or-compl = witness!

-- Testing witness tactic, uncomment if needed
-- private module _ where
--   open import Truncation.Propositional.Base

--   _ : ∀[ x ꞉ Bool ] ∀[ y ꞉ Bool ] ∃[ z ꞉ Bool ] (z ＝ x or y)
--   _ = witness!

--   _ : ∀[ x ꞉ Bool ] ∃[ f ꞉ (Bool → Bool → Bool) ] Π[ y ꞉ Bool ] (f x y ＝ not (f (not x) y))
--   _ = witness!

--   _ : ¬ ∃[ f ꞉ (Bool × Bool → Bool) ] Π[ x ꞉ Bool ] (f (x , false) ≠ f (x , false))
--   _ = witness!

--   module _ {r : Bool} where
--     _ : ∃[ x ꞉ Bool ] (x ＝ r)
--     _ = witness!

--   module _ {A : Type} {u : A} (a a′ : A) (z w r : Bool) (B : Type) {b c d e : B} where
--     _ : ∃[ x ꞉ Bool ] (x ＝ z)
--     _ = witness!

--     module _ {R : Type} {a u : Bool} {v : A} where
--       _ : ∃[ x ꞉ Bool ] (x ＝ r or a)
--       _ = witness!
