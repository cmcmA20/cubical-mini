{-# OPTIONS --safe #-}
module Data.Bool.Properties where

open import Meta.Prelude
open import Meta.Witness

open import Logic.Decidability
open import Logic.Exhaustibility
open import Logic.Omniscience

open import Combinatorics.Finiteness.Bishop.Manifest
open import Combinatorics.Finiteness.Bishop.Weak

open import Data.Empty.Base as ⊥
open import Data.Bool.Base as Bool public
open import Data.Bool.Path
open import Data.Bool.Instances.Finite
open import Data.Maybe.Base
open import Data.Reflects.Base as Reflects
open import Data.Reflects.Properties
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Unit.Base

private variable
  ℓᵃ ℓ ℓ′ ℓ″ : Level
  A : Type ℓᵃ
  P : Type ℓ
  Q : Type ℓ′
  R : Type ℓ″
  x y z b : Bool

universal : (Bool → A)
          ≃ A × A
universal = ≅→≃ $ iso
 (λ ch → ch true , ch false)
 (flip (Bool.rec fst snd))
 refl
 (fun-ext λ _ → fun-ext $ Bool.elim refl refl)

bool≃maybe⊤ : Bool ≃ Maybe ⊤
bool≃maybe⊤ = ≅→≃ $ iso to from (fun-ext ri) (fun-ext li) where
  to : Bool → Maybe ⊤
  to false = nothing
  to true  = just tt

  from : Maybe ⊤ → Bool
  from (just _) = true
  from nothing  = false

  ri : from section-of′ to
  ri (just _) = refl
  ri nothing  = refl

  li : from retraction-of′ to
  li false = refl
  li true  = refl

boolean-pred-ext : (f g : A → Bool) → f ⊆ g → g ⊆ f → f ＝ g
boolean-pred-ext f g p q = fun-ext λ _ → so-injₑ (prop-extₑ! p q)

-- if

if-true : ∀ {b} {t f : A} → ⌞ b ⌟ → (if b then t else f) ＝ t
if-true {b = true}  _  = refl

if-false : ∀ {b} {t f : A} → ⌞ not b ⌟ → (if b then t else f) ＝ f
if-false {b = false} _  = refl


-- negation

not-invol : ∀ x → not (not x) ＝ x
not-invol = witness!

≠→=not : ∀ x y → x ≠ y → x ＝ not y
≠→=not = witness!


-- conjunction

and-so-≃ : ⌞ x and y ⌟ ≃ ⌞ x ⌟ × ⌞ y ⌟
and-so-≃ = prop-extₑ! to from where
  to : ⌞ x and y ⌟ → ⌞ x ⌟ × ⌞ y ⌟
  to {(true)} = oh ,_
  from : ⌞ x ⌟ × ⌞ y ⌟ → ⌞ x and y ⌟
  from {(true)} = snd

and-true-≃ : is-true (x and y) ≃ (is-true x × is-true y)
and-true-≃ = so≃is-true ⁻¹ ∙ and-so-≃ ∙ ×-ap so≃is-true so≃is-true

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

not-and : ∀ x y → not (x and y) ＝ not x or not y
not-and = witness!


-- disjunction

or-so-≃
  : ⌞ x or y ⌟
  ≃ ( ⌞ x ⌟     × ⌞ not y ⌟
  ⊎   ⌞ not x ⌟ × ⌞ y ⌟
  ⊎   ⌞ x ⌟     × ⌞ y ⌟ )
or-so-≃ = prop-extₑ (hlevel 1) go to from where
  to : ⌞ x or y ⌟ → ⌞ x ⌟ × ⌞ not y ⌟ ⊎ ⌞ not x ⌟ × ⌞ y ⌟ ⊎ ⌞ x ⌟ × ⌞ y ⌟
  to {(false)}          p = inr (inl (oh , p))
  to {(true)} {(false)} p = inl (oh , oh)
  to {(true)} {(true)}  p = inr (inr (oh , oh))

  from : ⌞ x ⌟ × ⌞ not y ⌟ ⊎ ⌞ not x ⌟ × ⌞ y ⌟ ⊎ ⌞ x ⌟ × ⌞ y ⌟ → ⌞ x or y ⌟
  from {(false)} (inr (inl p)) = p .snd
  from {(true)} _ = oh

  go : is-prop (⌞ x ⌟ × ⌞ not y ⌟ ⊎ ⌞ not x ⌟ × ⌞ y ⌟ ⊎ ⌞ x ⌟ × ⌞ y ⌟)
  go {(false)} = disjoint-⊎-is-prop (hlevel 1) (disjoint-⊎-is-prop! λ ()) λ ()
  go {(true)} {(false)} = disjoint-⊎-is-prop (hlevel 1) (disjoint-⊎-is-prop! λ ()) ([ (λ()) , (λ()) ]ᵤ ∘ snd)
  go {(true)} {(true)} = disjoint-⊎-is-prop (hlevel 1) (disjoint-⊎-is-prop! λ ()) λ ()

-- TODO refactor
or-true-≃
  : is-true (x or y)
  ≃ ( (is-true  x × is-false y)
  ⊎   (is-false x × is-true  y)
  ⊎   (is-true  x × is-true  y) )
or-true-≃ = prop-extₑ (hlevel 1) go to from where
  to : is-true (x or y)
     → ((is-true x × is-false y) ⊎ (is-false x × is-true y) ⊎ (is-true x × is-true y))
  to {(false)} {(false)} p = false! p
  to {(false)} {(true)}  _ = inr (inl (refl , refl))
  to {(true)}  {(false)} _ = inl (refl , refl)
  to {(true)}  {(true)}  _ = inr (inr (refl , refl))

  from : ((is-true x × is-false y) ⊎ (is-false x × is-true y) ⊎ (is-true x × is-true y))
       → is-true (x or y)
  from {(false)} {(false)}   = [ fst , [ snd , snd ]ᵤ ]ᵤ
  from {(false)} {(true)}  _ = refl
  from {(true)}            _ = refl

  go : is-prop (is-true x × is-false y ⊎ is-false x × is-true y ⊎ is-true x × is-true y)
  go {x} {y} = disjoint-⊎-is-prop (hlevel 1)
    (disjoint-⊎-is-prop! (λ z → false! (z .fst .fst ⁻¹ ∙ z .snd .fst)))
    λ z → [ (λ w → false! (w .fst ⁻¹ ∙ z .fst .fst))
          , (λ w → false! (z .fst .snd ⁻¹ ∙ w .snd)) ]ᵤ
        (z .snd)

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

not-or : ∀ x y → not (x or y) ＝ not x and not y
not-or = witness!


-- xor

-- FIXME XXX
reflects-xor : ∀ {x y} → Reflects (not x ＝ y) (x xor y)
reflects-xor {(false)} = auto
reflects-xor {(true)}  = auto

xor-assoc : ∀ x y z → (x xor y) xor z ＝ x xor y xor z
xor-assoc = witness!

not-xor-l : ∀ x y → not (x xor y) ＝ not x xor y
not-xor-l = witness!

not-xor-r : ∀ x y → not (x xor y) ＝ x xor not y
not-xor-r = witness!


-- distributivity

and-distrib-xor-l : ∀ x y z → x and (y xor z) ＝ (x and y) xor (x and z)
and-distrib-xor-l = witness!

and-distrib-xor-r : ∀ x y z → (x xor y) and z ＝ (x and z) xor (y and z)
and-distrib-xor-r = witness!

and-distrib-or-l : ∀ x y z → x and (y or z) ＝ (x and y) or (x and z)
and-distrib-or-l = witness!

and-distrib-or-r : ∀ x y z → (x or y) and z ＝ (x and z) or (y and z)
and-distrib-or-r = witness!


-- -- Testing witness tactic, uncomment if needed
-- private module _ where
--   open import Data.Truncation.Propositional.Base

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
--       beb : Σ[ x ꞉ Bool ] (x ＝ r or a)
--       beb = witness!
