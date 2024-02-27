{-# OPTIONS --safe #-}
module Data.Bool.Path where

open import Foundations.Base hiding (_∙_)
open import Foundations.Equiv

open import Meta.Groupoid
open import Meta.Search.HLevel
open import Meta.Underlying

open import Structures.IdentitySystem.Base

open import Data.Empty.Base as ⊥
open import Data.Unit.Base as ⊤

open import Data.Bool.Base as Bool

_==_ : Bool → Bool → Bool
false == false = true
true  == true  = true
_     == _     = false

false≠true : false ≠ true
false≠true p = subst (λ b → ⟦ not b ⟧ᵇ) p tt

true≠false : true ≠ false
true≠false = false≠true ∘ sym

Code : Bool → Bool → Type
Code b₁ b₂ = ⟦ b₁ == b₂ ⟧ᵇ

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

⟦-⟧ᵇ-inj : ⟦ b₁ ⟧ᵇ ≃ ⟦ b₂ ⟧ᵇ → b₁ ＝ b₂
⟦-⟧ᵇ-inj {(false)} {(false)} _ = refl
⟦-⟧ᵇ-inj {(false)} {(true)}  f = ⊥.rec $ᴱ (f ⁻¹) # tt
⟦-⟧ᵇ-inj {(true)}  {(false)} f = ⊥.rec $ᴱ f # tt
⟦-⟧ᵇ-inj {(true)}  {(true)}  _ = refl

⟦-⟧ᵇ≃true : ⟦ b ⟧ᵇ ≃ (b ＝ true)
⟦-⟧ᵇ≃true = go ∙ identity-system-gives-path identity-system where
  go : ⟦ b ⟧ᵇ ≃ ⟦ b == true ⟧ᵇ
  go {(false)} = prop-extₑ! id id
  go {(true)}  = prop-extₑ! id id

¬⟦-⟧ᵇ≃false : (¬ ⟦ b ⟧ᵇ) ≃ (b ＝ false)
¬⟦-⟧ᵇ≃false = go ∙ identity-system-gives-path identity-system where
  go : (¬ ⟦ b ⟧ᵇ) ≃ ⟦ b == false ⟧ᵇ
  go {(false)} = prop-extₑ! _ λ _ → id
  go {(true)}  = prop-extₑ! (λ f → f _) (λ f _ → f)
