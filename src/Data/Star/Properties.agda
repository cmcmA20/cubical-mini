{-# OPTIONS --safe #-}
module Data.Star.Properties where

open import Foundations.Base
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Star.Base

private variable
  ℓa ℓb ℓ ℓ′ : Level
  A : 𝒰 ℓa
  B : 𝒰 ℓb
  R : A → A → 𝒰 ℓ
  S : B → B → 𝒰 ℓ′
  x y z : A

star-len : Star R x y → ℕ
star-len (ε _)   = 0
star-len (_ ◅ s) = suc (star-len s)

star-trans-len
  : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y z : A}
  → (sxy : Star R x y) (syz : Star R y z)
  → star-len (sxy ∙ syz) ＝ star-len sxy + star-len syz
star-trans-len (ε u)     (ε v)     = refl
star-trans-len (ε u)     (v ◅ syz) = ap suc (star-trans-len refl syz)
star-trans-len (_ ◅ sxy) syz       = ap suc (star-trans-len sxy  syz)

star-◅+-len
  : (sxy : Star R x y) (ryz : R y z)
  → star-len (sxy ◅+ ryz) ＝ suc (star-len sxy)
star-◅+-len sxy ryz = star-trans-len sxy (star-sng ryz) ∙ +-comm (star-len sxy) 1

star-map-len
  : {f : A → B} {r : ∀ {a b} → R a b → S (f a) (f b)}
  → (sxy : Star R x y)
  → star-len {R = S} (star-map r sxy) ＝ star-len sxy
star-map-len (ε e)     = refl
star-map-len (_ ◅ sxy) = ap suc (star-map-len sxy)
