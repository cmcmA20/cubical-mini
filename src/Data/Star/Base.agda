{-# OPTIONS --safe #-}
module Data.Star.Base where

open import Foundations.Base
open import Data.Nat.Base
open import Data.Nat.Properties

-- aka reflexive-transitive closure
data Star {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : A → A → 𝒰 (ℓᵃ ⊔ ℓ) where
  ε    : ∀ {x y} → x ＝ y → Star R x y
  _◅_ : ∀ {x y z} → R x y → Star R y z → Star R x z

record Substar {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : 𝒰 (ℓᵃ ⊔ ℓ) where
  constructor sst
  field
    from : A
    to   : A
    path : Star R from to

open Substar public

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  R : A → A → 𝒰 ℓ
  S : B → B → 𝒰 ℓ′

star-sng : ∀ {x y} → R x y → Star R x y
star-sng rxy = rxy ◅ ε refl

star-len : ∀ {x y} → Star R x y → ℕ
star-len (ε _)    = 0
star-len (_ ◅ s) = suc (star-len s)

star-trans : {x y z : A}
           → Star R x y → Star R y z → Star R x z
star-trans {R} {z} (ε e)      syz = subst (λ q → Star R q z) (e ⁻¹) syz
star-trans         (xw ◅ swy) syz = xw ◅ star-trans swy syz

_◅+_ : ∀ {x y z} → Star R x y → R y z → Star R x z
sxy ◅+ ryz = star-trans sxy (star-sng ryz)

-- TODO move to properties
star-trans-len : {x y z : A}
               → (sxy : Star R x y) → (syz : Star R y z)
               → star-len (star-trans sxy syz) ＝ star-len sxy + star-len syz
star-trans-len {R} {z} (ε e)         =
  Jₚ (λ x′ e′ → (s′ : Star R x′ z) → star-len (subst (λ q → Star R q z) (e′ ⁻¹) s′) ＝ star-len s′)
     (λ s′ → ap star-len (subst-refl {B = λ q → Star R q z} s′))
     e
star-trans-len         (_ ◅ sxy) syz = ap suc (star-trans-len sxy syz)

star-◅+-len : {x y z : A}
            → (sxy : Star R x y) → (ryz : R y z)
            → star-len (sxy ◅+ ryz) ＝ suc (star-len sxy)
star-◅+-len sxy ryz = star-trans-len sxy (star-sng ryz) ∙ +-comm (star-len sxy) 1

star-map : {x y : A} {f : A → B}
         → (∀ {a b} → R a b → S (f a) (f b))
         → Star R x y → Star S (f x) (f y)
star-map {f} fp (ε e)      = ε (ap f e)
star-map     fp (xw ◅ swy) = fp xw ◅ star-map fp swy

instance
  Refl-Star : Refl (Star R)
  Refl-Star .refl = ε refl

  Trans-Star : Trans (Star R)
  Trans-Star ._∙_ = star-trans
