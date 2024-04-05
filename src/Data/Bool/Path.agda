{-# OPTIONS --safe #-}
module Data.Bool.Path where

open import Meta.Prelude

open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

open import Data.Empty.Base as ⊥
open import Data.Unit.Base as ⊤

open import Data.Bool.Base as Bool

_==_ : Bool → Bool → Bool
false == false = true
true  == true  = true
_     == _     = false

false≠true : false ≠ true
false≠true p = subst (λ b → is-true (not b)) p tt

true≠false : true ≠ false
true≠false = false≠true ∘ symₚ

Code : Bool → Bool → Type
Code b₁ b₂ = is-true (b₁ == b₂)

code-refl : (b : Bool) → Code b b
code-refl false = tt
code-refl true  = tt

decode : ∀ b₁ b₂ → Code b₁ b₂ → b₁ ＝ b₂
decode false false _ = refl
decode true  true  _ = refl

code-is-prop : ∀ b₁ b₂ → is-prop (Code b₁ b₂)
code-is-prop false false = hlevel!
code-is-prop false true  = hlevel!
code-is-prop true  false = hlevel!
code-is-prop true  true  = hlevel!

identity-system : is-identity-system Code code-refl
identity-system = set-identity-system code-is-prop (decode _ _)

private variable
  ℓ : Level
  b b₁ b₂ : Bool
  n : HLevel

bool-is-set : is-set Bool
bool-is-set = identity-system→is-of-hlevel 1 identity-system code-is-prop

instance
  H-Level-Bool : ∀ {n} → H-Level (2 + n) Bool
  H-Level-Bool = hlevel-basic-instance 2 bool-is-set

bool-is-of-hlevel : ∀ n → is-of-hlevel (2 + n) Bool
bool-is-of-hlevel _ = hlevel _

instance
  decomp-hlevel-bool : goal-decomposition (quote is-of-hlevel) Bool
  decomp-hlevel-bool = decomp (quote bool-is-of-hlevel) [ `level-minus 2 ]

is-true-inj : is-true b₁ ≃ is-true b₂ → b₁ ＝ b₂
is-true-inj {(false)} {(false)} _ = refl
is-true-inj {(false)} {(true)}  f = ⊥.rec $ f ⁻¹ $ tt
is-true-inj {(true)}  {(false)} f = ⊥.rec $ f    $ tt
is-true-inj {(true)}  {(true)}  _ = refl

is-true≃is-trueₚ : is-true b ≃ is-trueₚ b
is-true≃is-trueₚ = go ∙ identity-system-gives-path identity-system where
  go : is-true b ≃ is-true (b == true)
  go {(false)} = prop-extₑ! refl refl
  go {(true)}  = prop-extₑ! refl refl

¬is-true≃is-falseₚ : (¬ is-true b) ≃ is-falseₚ b
¬is-true≃is-falseₚ = go ∙ identity-system-gives-path identity-system where
  go : (¬ is-true b) ≃ is-true (b == false)
  go {(false)} = prop-extₑ! _ λ _ → refl
  go {(true)}  = prop-extₑ! (λ f → f _) (λ f _ → f)
