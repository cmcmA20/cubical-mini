{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.Transport

open import Meta.Search.Decidable
open import Meta.Search.Discrete
open import Meta.Search.Exhaustible
open import Meta.Search.Finite.Bishop
open import Meta.Search.Finite.ManifestBishop
open import Meta.Search.HLevel
open import Meta.Search.Omniscient
open import Meta.Underlying
open import Meta.Witness

open import Data.Empty.Base as ⊥
open import Data.Bool.Base as Bool public
open import Data.Bool.Path
open import Data.Bool.Instances.Finite
open import Data.Bool.Instances.Underlying
open import Data.Sum.Base
open import Data.Sum.Path

private variable
  ℓᵃ : Level
  A : Type ℓᵃ
  x y : Bool

universal : (Bool → A)
          ≃ A × A
universal = iso→equiv
  $ (λ ch → ch true , ch false)
  , iso (flip (Bool.rec fst snd))
        (λ _ → refl)
        (λ _ → fun-ext $ Bool.elim refl refl)

boolean-pred-ext : (f g : A → Bool) → f ⊆ g → g ⊆ f → f ＝ g
boolean-pred-ext f g p q i a with f a | recall f a | g a | recall g a
... | false | ⟪ _ ⟫ | false | ⟪ _ ⟫ = false
... | false | ⟪ u ⟫ | true  | ⟪ v ⟫ =
  let q′ = subst² (λ φ ψ → ⟦ φ ⟧ᵇ → ⟦ ψ ⟧ᵇ) v u (q {a})
  in ⊥.rec {A = false ＝ true} (q′ tt) i
... | true  | ⟪ u ⟫ | false | ⟪ v ⟫ =
  let p′ = subst² (λ φ ψ → ⟦ φ ⟧ᵇ → ⟦ ψ ⟧ᵇ) u v (p {a})
  in ⊥.rec {A = true ＝ false} (p′ tt) i
... | true  | ⟪ _ ⟫ | true  | ⟪ _ ⟫ = true

-- FIXME very slow hlevel inference
or-true-≃
  : (x or y ＝ true)
  ≃ ( ((x ＝ true ) × (y ＝ false))
  ⊎   ((x ＝ false) × (y ＝ true ))
  ⊎   ((x ＝ true ) × (y ＝ true )) )
or-true-≃ = prop-extₑ (helper _ _) go to from where
  to : (x or y ＝ true) → (((x ＝ true) × (y ＝ false)) ⊎ ((x ＝ false) × (y ＝ true)) ⊎ ((x ＝ true) × (y ＝ true)))
  to {(false)} {(false)} p = ⊥.rec $ᴱ false≠true p
  to {(false)} {(true)}  _ = inr (inl (refl , refl))
  to {(true)}  {(false)} _ = inl (refl , refl)
  to {(true)}  {(true)}  _ = inr (inr (refl , refl))

  from : (((x ＝ true) × (y ＝ false)) ⊎ ((x ＝ false) × (y ＝ true)) ⊎ ((x ＝ true) × (y ＝ true))) → (x or y ＝ true)
  from {(false)} {(false)}   = [ fst , [ snd , snd ]ᵤ ]ᵤ
  from {(false)} {(true)}  _ = refl
  from {(true)}            _ = refl

  helper = path-is-of-hlevel′ 1 bool-is-set

  go : is-prop ((x ＝ true) × (y ＝ false) ⊎ (x ＝ false) × (y ＝ true) ⊎ (x ＝ true) × (y ＝ true))
  go {x} {y} = disjoint-⊎-is-prop (×-is-of-hlevel 1 (helper _ _) (helper _ _))
                                  (disjoint-⊎-is-prop (×-is-of-hlevel 1 (helper _ _) (helper _ _))
                                                      (×-is-of-hlevel 1 (helper _ _) (helper _ _))
                                     λ z → false≠true (sym (z .fst .fst) ∙ z .snd .fst))
    λ z → [ (λ w → false≠true (sym (w .fst) ∙ z .fst .fst)) , (λ w → false≠true (sym (z .fst .snd) ∙ w .snd)) ]ᵤ (z .snd)

module or-true-≃ {x} {y} = Equiv (or-true-≃ {x} {y})

-- FIXME very slow hlevel inference
and-true-≃ : (x and y ＝ true) ≃ ((x ＝ true) × (y ＝ true))
and-true-≃ = prop-extₑ (go _ _) (×-is-of-hlevel 1 (go _ _) (go _ _)) to from where
  go = path-is-of-hlevel′ 1 bool-is-set

  to : x and y ＝ true → (x ＝ true) × (y ＝ true)
  to {(false)} p = ⊥.rec $ᴱ false≠true p
  to {(true)}  p = refl , p

  from : (x ＝ true) × (y ＝ true) → x and y ＝ true
  from {(false)} p = p .fst
  from {(true)}  p = p .snd

module and-true-≃ {x} {y} = Equiv (and-true-≃ {x} {y})

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
