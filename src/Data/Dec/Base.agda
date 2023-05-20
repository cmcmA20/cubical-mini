{-# OPTIONS --safe #-}
module Data.Dec.Base where

open import Foundations.Base

open import Data.Bool.Base public
import      Data.Empty.Base as ⊥

open import Meta.Reflection.Record

open import Structures.Instances.Negation public

private variable
  ℓ ℓ′ : Level
  A P : Type ℓ
  B Q : Type ℓ′
  a b : Bool

-- some predicates can be reflected in booleans

data Reflects {ℓ} (P : Type ℓ) : Bool → Type ℓ where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false

-- FIXME just show equivalence to sums and reuse their h-levels
is-prop→reflects-is-prop : is-prop P → is-prop (Reflects P b)
is-prop→reflects-is-prop P-prop (ofʸ  p) (ofʸ  p′) = ap ofʸ (P-prop _ _)
is-prop→reflects-is-prop P-prop (ofⁿ ¬p) (ofⁿ ¬p′) = ap ofⁿ (fun-ext λ p → ⊥.rec (¬p p))

of : if b then A else ¬ A → Reflects A b
of {b = false} ¬a = ofⁿ ¬a
of {b = true }  a = ofʸ a

invert : Reflects P b → if b then P else ¬ P
invert (ofʸ  p) = p
invert (ofⁿ ¬p) = ¬p

¬-reflects : Reflects P b → Reflects (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

reflects-det : Reflects P a → Reflects P b → a ＝ b
reflects-det (ofʸ  p) (ofʸ  p′) = refl
reflects-det (ofʸ  p) (ofⁿ ¬p′) = ⊥.rec (¬p′ p)
reflects-det (ofⁿ ¬p) (ofʸ  p′) = ⊥.rec (¬p p′)
reflects-det (ofⁿ ¬p) (ofⁿ ¬p′) = refl


-- witness of a predicate being (already) decided

infix 2 _because_
record Dec {ℓ} (P : Type ℓ) : Type ℓ where
  constructor _because_
  field
    does  : Bool
    proof : Reflects P does
open Dec public

module _ {ℓ} (P : Type ℓ) where
  dec-record-iso : Iso (Dec P) (Σ[ does ꞉ Bool ] Reflects P does)
  unquoteDef dec-record-iso = define-record-iso dec-record-iso (quote Dec)

pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

recompute : Dec A → @0 A → A
recompute (yes a) _  = a
recompute (no ¬a) 0a = ⊥.rec (¬a 0a)

rec : (A → B) → (¬ A → B) → Dec A → B
rec ifyes ifno (yes p) = ifyes p
rec ifyes ifno (no ¬p) = ifno ¬p

⌊_⌋ : Dec A → Bool
⌊ b because _ ⌋ = b
