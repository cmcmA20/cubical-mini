{-# OPTIONS --safe #-}
module Data.Bool.Path where

open import Meta.Prelude

open import Meta.Extensionality

open import Data.Bool.Base  as Bool
open import Data.Empty.Base as ⊥
open import Data.Unit.Base  as ⊤

_==_ : Bool → Bool → Bool
false == false = true
true  == true  = true
_     == _     = false

false≠true : false ≠ true
false≠true p = substₚ (λ b → is-true (not b)) p tt

true≠false : true ≠ false
true≠false = false≠true ∘ sym

Extensional-Bool : Extensional Bool 0ℓ
Extensional-Bool .Pathᵉ b₁ b₂ = is-true (b₁ == b₂)
Extensional-Bool .reflᵉ false = tt
Extensional-Bool .reflᵉ true  = tt
Extensional-Bool .idsᵉ = set-identity-system (λ _ _ → hlevel 1) (decode _ _)
  where
  decode : ∀ b₁ b₂ → is-true (b₁ == b₂) → b₁ ＝ b₂
  decode false false _ = refl
  decode true  true  _ = refl
-- {-# INCOHERENT Extensional-Bool #-} -- don't use it for now

private variable
  ℓ : Level
  b b₁ b₂ : Bool
  n : HLevel

instance
  H-Level-Bool : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n Bool
  H-Level-Bool ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 $ identity-system→is-of-hlevel 1
    (Extensional-Bool .idsᵉ) λ _ _ → hlevel 1
  {-# OVERLAPPING H-Level-Bool #-}

is-true-inj : is-true b₁ ≃ is-true b₂ → b₁ ＝ b₂
is-true-inj {(false)} {(false)} _ = refl
is-true-inj {(false)} {(true)}  f = ⊥.rec $ f ⁻¹ $ tt
is-true-inj {(true)}  {(false)} f = ⊥.rec $ f    $ tt
is-true-inj {(true)}  {(true)}  _ = refl

is-true≃is-trueₚ : is-true b ≃ is-trueₚ b
is-true≃is-trueₚ = go ∙ identity-system-gives-path (Extensional-Bool .idsᵉ) where
  go : is-true b ≃ is-true (b == true)
  go {(false)} = prop-extₑ! refl refl
  go {(true)}  = prop-extₑ! refl refl

¬is-true≃is-falseₚ : (¬ is-true b) ≃ is-falseₚ b
¬is-true≃is-falseₚ = go ∙ identity-system-gives-path (Extensional-Bool .idsᵉ) where
  go : (¬ is-true b) ≃ is-true (b == false)
  go {(false)} = prop-extₑ! _ λ _ → refl
  go {(true)}  = prop-extₑ! (λ f → f _) (λ f _ → f)
