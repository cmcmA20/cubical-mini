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
open import Data.Bool.Instances.Underlying
open import Data.Maybe.Base
open import Data.Reflects.Base
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Unit.Base

private variable
  ℓᵃ : Level
  A : Type ℓᵃ
  x y : Bool

universal : (Bool → A)
          ≃ A × A
universal = ≅→≃
  $ (λ ch → ch true , ch false)
  , iso (flip (Bool.rec fst snd))
        (λ _ → refl)
        (λ _ → fun-ext $ Bool.elim refl refl)

bool≃maybe⊤ : Bool ≃ Maybe ⊤
bool≃maybe⊤ = ≅→≃ $ to , iso from ri li where
  to : Bool → Maybe ⊤
  to false = nothing
  to true  = just tt

  from : Maybe ⊤ → Bool
  from (just _) = true
  from nothing  = false

  ri : from is-right-inverse-of to
  ri (just _) = refl
  ri nothing  = refl

  li : from is-left-inverse-of to
  li false = refl
  li true  = refl

boolean-pred-ext : (f g : A → Bool) → f ⊆ g → g ⊆ f → f ＝ g
boolean-pred-ext f g p q i a with f a | recall f a | g a | recall g a
... | false | ⟪ _ ⟫ | false | ⟪ _ ⟫ = false
... | false | ⟪ u ⟫ | true  | ⟪ v ⟫ =
  let q′ = subst² (λ φ ψ → is-true φ → is-true ψ) v u (q {a})
  in ⊥.rec {A = false ＝ true} (q′ tt) i
... | true  | ⟪ u ⟫ | false | ⟪ v ⟫ =
  let p′ = subst² (λ φ ψ → is-true φ → is-true ψ) u v (p {a})
  in ⊥.rec {A = true ＝ false} (p′ tt) i
... | true  | ⟪ _ ⟫ | true  | ⟪ _ ⟫ = true


reflects-id : ∀ {x} → Reflects (is-true x) x
reflects-id {(false)} = ofⁿ id
reflects-id {(true)}  = ofʸ tt

-- negation

reflects-not : ∀ {x} → Reflects (¬ is-true x) (not x)
reflects-not {(false)} = ofʸ id
reflects-not {(true)}  = ofⁿ (_$ tt)

not-invol : ∀ x → not (not x) ＝ x
not-invol = witness!

≠→=not : ∀ x y → x ≠ y → x ＝ not y
≠→=not = witness!


-- conjunction

and-true-≃ : is-trueₚ (x and y) ≃ (is-trueₚ x × is-trueₚ y)
and-true-≃ = prop-extₑ! to from where
  to : is-trueₚ (x and y) → (is-trueₚ x × is-trueₚ y)
  to {(false)} p = ⊥.rec $ false≠true p
  to {(true)}  p = refl , p

  from : (is-trueₚ x × is-trueₚ y) → is-trueₚ (x and y)
  from {(false)} p = p .fst
  from {(true)}  p = p .snd

module and-true-≃ {x} {y} = Equiv (and-true-≃ {x} {y})

reflects-and : ∀ {x y} → Reflects (is-true x × is-true y) (x and y)
reflects-and {x = false}            = ofⁿ fst
reflects-and {x = true} {y = false} = ofⁿ snd
reflects-and {x = true} {y = true}  = ofʸ (tt , tt)

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

or-true-≃
  : is-trueₚ (x or y)
  ≃ ( (is-trueₚ  x × is-falseₚ y)
  ⊎   (is-falseₚ x × is-trueₚ  y)
  ⊎   (is-trueₚ  x × is-trueₚ  y) )
or-true-≃ = prop-extₑ (hlevel 1) go to from where
  to : is-trueₚ (x or y)
     → ((is-trueₚ x × is-falseₚ y) ⊎ (is-falseₚ x × is-trueₚ y) ⊎ (is-trueₚ x × is-trueₚ y))
  to {(false)} {(false)} p = ⊥.rec $ false≠true p
  to {(false)} {(true)}  _ = inr (inl (refl , refl))
  to {(true)}  {(false)} _ = inl (refl , refl)
  to {(true)}  {(true)}  _ = inr (inr (refl , refl))

  from : ((is-trueₚ x × is-falseₚ y) ⊎ (is-falseₚ x × is-trueₚ y) ⊎ (is-trueₚ x × is-trueₚ y))
       → is-trueₚ (x or y)
  from {(false)} {(false)}   = [ fst , [ snd , snd ]ᵤ ]ᵤ
  from {(false)} {(true)}  _ = refl
  from {(true)}            _ = refl

  go : is-prop (is-trueₚ x × is-falseₚ y ⊎ is-falseₚ x × is-trueₚ y ⊎ is-trueₚ x × is-trueₚ y)
  go {x} {y} = disjoint-⊎-is-prop (hlevel 1)
    (disjoint-⊎-is-prop! λ z → false≠true (z .fst .fst ⁻¹ ∙ z .snd .fst))
    λ z → [ (λ w → false≠true (w .fst ⁻¹ ∙ z .fst .fst)) , (λ w → false≠true (z .fst .snd ⁻¹ ∙ w .snd)) ]ᵤ (z .snd)

module or-true-≃ {x} {y} = Equiv (or-true-≃ {x} {y})

-- TODO reflection to a These structure
reflects-or : ∀ {x y} → Reflects (is-true x ⊎ is-true y) (x or y)
reflects-or {x = false} {y = false} = ofⁿ [ id , id ]ᵤ
reflects-or {x = false} {y = true}  = ofʸ (inr tt)
reflects-or {x = true}              = ofʸ (inl tt)

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
reflects-xor : ∀ {x y} → Reflects (not x ＝ y) (x xor y)
reflects-xor {x = false} {y = false} = ofⁿ true≠false
reflects-xor {x = false} {y = true}  = ofʸ refl
reflects-xor {x = true}  {y = false} = ofʸ refl
reflects-xor {x = true}  {y = true}  = ofⁿ false≠true

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
--       beb : Σ[ x ꞉ Bool ] (x ＝ r or a)
--       beb = witness!
