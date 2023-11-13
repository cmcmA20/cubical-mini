{-# OPTIONS --safe #-}
module Data.Bool.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

open import Data.Empty.Base as ⊥
open import Data.Unit.Base as ⊤

open import Data.Bool.Base as Bool public

_==_ : Bool → Bool → Bool
false == false = true
true  == true  = true
_     == _     = false

false≠true : false ≠ true
false≠true p = subst (λ b → ⟦ not b ⟧ᵇ) p tt

true≠false : true ≠ false
true≠false = false≠true ∘ sym

Code : Bool → Bool → Type
Code false false = ⊤
Code true  true  = ⊤
Code _     _     = ⊥

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

instance
  H-Level-Bool : ∀ {n} → H-Level (2 + n) Bool
  H-Level-Bool = hlevel-basic-instance 2 $ identity-system→is-of-hlevel 1 identity-system code-is-prop

⟦-⟧ᵇ≃true : {b : Bool} → ⟦ b ⟧ᵇ ≃ (b ＝ true)
⟦-⟧ᵇ≃true {(false)} = prop-extₑ! (λ x → ⊥.rec x) false≠true
⟦-⟧ᵇ≃true {(true)}  = prop-extₑ! (λ _ → refl) _
