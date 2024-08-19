{-# OPTIONS --safe --no-exact-split #-}
module Data.Bool.Base where

open import Foundations.Prelude

open import Data.Empty.Base as ⊥
  using (⊥-is-prop)
open import Data.Unit.Base
  using (⊤-is-contr)

open import Agda.Builtin.Bool public

private variable
  ℓ : Level
  A : Type ℓ
  b b₁ b₂ : Bool

elim : {P : Bool → Type ℓ} (t : P true) (f : P false) (b : Bool) → P b
elim _ f false = f
elim t _ true  = t

rec : A → A → Bool → A
rec = elim

not : Bool → Bool
not true = false
not false = true

infixr 5 _or_ _xor_
_or_ : Bool → Bool → Bool
false or x = x
true  or _ = true

infixr 6 _and_ _implies_ _equals_
_and_ : Bool → Bool → Bool
false and _ = false
true  and x = x

_xor_ : Bool → Bool → Bool
false xor x = x
true  xor x = not x

_equals_ : Bool → Bool → Bool
false equals y = not y
true  equals y = y

_implies_ : Bool → Bool → Bool
true implies false = false
_    implies _     = true

infix 0 if_then_else_
if_then_else_ : Bool → A → A → A
if b then tr else fa = rec tr fa b
{-# NOINLINE if_then_else_ #-}

is-true : Bool → Type
is-true b = b ＝ true

is-false : Bool → Type
is-false b = b ＝ false


-- Automation

-- Idris vibes
record So (b : Bool) : Type where
  field is-so : if b then ⊤ else ⊥

pattern oh = record { is-so = tt }

¬-so-false : ¬ So false
¬-so-false ()

not-so : ∀{b} → ¬ So b → So (not b)
not-so {(false)} _ = oh
not-so {(true)} f = ⊥.rec (f oh)

so-injₑ : So b₁ ≃ So b₂ → b₁ ＝ b₂
so-injₑ {(false)} {(false)} _ = refl
so-injₑ {(false)} {(true)}  f = ⊥.rec $ ¬-so-false (f ⁻¹ $ oh)
so-injₑ {(true)}  {(false)} f = ⊥.rec $ ¬-so-false (f    $ oh)
so-injₑ {(true)}  {(true)}  _ = refl

so-inj : So b₁ ＝ So b₂ → b₁ ＝ b₂
so-inj = so-injₑ ∘ =→≃

instance
  Oh : So true
  Oh = oh

  H-Level-So : ∀ {b n} → H-Level (suc n) (So b)
  H-Level-So {(false)} = hlevel-prop-instance λ ()
  H-Level-So {(true)}  = hlevel-prop-instance λ where oh oh → refl

  Underlying-Bool : Underlying Bool
  Underlying-Bool .Underlying.ℓ-underlying = 0ℓ
  Underlying-Bool .Underlying.⌞_⌟ = So

  ×-So : ×-notation (So b₁) (So b₂) (So (b₁ and b₂))
  ×-So {b₁ = true} {b₂} ._×_ _ = refl

  ⇒-So : ⇒-notation (So b₁) (So b₂) (So (b₁ implies b₂))
  ⇒-So {b₁ = true} {b₂ = true} ._⇒_ _ _ = oh
