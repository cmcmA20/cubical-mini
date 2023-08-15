{-# OPTIONS --safe #-}
module Data.Bool.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

open import Data.Empty.Base
open import Data.Unit.Instances.HLevel

open import Data.Bool.Base public

_==_ : Bool → Bool → Bool
false == false = true
true  == true  = true
_     == _     = false

-- only for educational purpose
-- module _ where private
--   open import Data.Sum.Instances.HLevel
--   bool-as-sum : Bool ≃ (⊤ ⊎ ⊤)
--   bool-as-sum = iso→equiv 𝔯
--     where
--     𝔯 : Iso _ _
--     𝔯 .fst false = inl tt
--     𝔯 .fst true  = inr tt
--     𝔯 .snd .is-iso.inv (inl _) = false
--     𝔯 .snd .is-iso.inv (inr _) = true
--     𝔯 .snd .is-iso.rinv (inl _) = refl
--     𝔯 .snd .is-iso.rinv (inr _) = refl
--     𝔯 .snd .is-iso.linv false = refl
--     𝔯 .snd .is-iso.linv true  = refl

--   instance
--     bool-is-set : is-set Bool
--     bool-is-set = is-of-hlevel-≃ 2 bool-as-sum hlevel!

--   bool-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) Bool
--   bool-is-of-hlevel n = is-of-hlevel-+-left 2 n bool-is-set

--   false≠true : false ≠ true
--   false≠true = ⊎-disjoint ∘ ap (bool-as-sum .fst)

false≠true : false ≠ true
false≠true p = subst (λ b → ⟦ not b ⟧ᵇ) p tt

true≠false : true ≠ false
true≠false = false≠true ∘ sym

module bool-path-code where

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

  bool-identity-system : is-identity-system Code code-refl
  bool-identity-system = set-identity-system code-is-prop (decode _ _)

instance
  bool-is-set : is-set Bool
  bool-is-set = identity-system→hlevel 1 bool-path-code.bool-identity-system bool-path-code.code-is-prop

bool-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) Bool
bool-is-of-hlevel n = is-of-hlevel-+-left 2 n bool-is-set
