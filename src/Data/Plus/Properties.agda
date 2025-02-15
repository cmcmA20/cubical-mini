{-# OPTIONS --safe #-}
module Data.Plus.Properties where

open import Foundations.Base

open import Data.Empty.Base
open import Data.Acc.Base
open import Data.Acc.Properties
open import Data.Sum.Base
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Plus.Base
open import Data.Star.Base
open import Data.Star.Properties

private variable
  ℓ ℓa : Level
  A B : 𝒰 ℓ
  R S : A → A → 𝒰 ℓ
  x y z : A

plus-len : Plus R x y → ℕ
plus-len [ _ ]⁺   = 1
plus-len (_ ◅⁺ p) = suc (plus-len p)

plus-trans-len
  : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y z : A}
  → (pxy : Plus R x y) (pyz : Plus R y z)
  → plus-len (pxy ∙ pyz) ＝ plus-len pxy + plus-len pyz
plus-trans-len [ _ ]⁺     pyz = refl
plus-trans-len (_ ◅⁺ pxy) pyz = ap suc (plus-trans-len pxy pyz)

plus-◅⁺∷-len
  : (pxy : Plus R x y) (ryz : R y z)
  → plus-len (pxy ◅⁺∷ ryz) ＝ suc (plus-len pxy)
plus-◅⁺∷-len pxy ryz = plus-trans-len pxy [ ryz ]⁺ ∙ +-comm (plus-len pxy) 1

plus-map-len
  : {f : A → B} {r : ∀ {a b} → R a b → S (f a) (f b)}
  → (pxy : Plus R x y)
  → plus-len {R = S} (plus-map r pxy) ＝ plus-len pxy
plus-map-len [ _ ]⁺      = refl
plus-map-len (_ ◅⁺ pxy) = ap suc (plus-map-len pxy)

-- interaction with Star

plus→star : Plus R x y → Star R x y
plus→star [ rxy ]⁺   = rxy ◅ ε refl
plus→star (rxw ◅⁺ p) = rxw ◅ plus→star p

plus-uncons : ∀ {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y : A}
            → Plus R x y → Σ[ z ꞉ A ] (R x z × Star R z y)
plus-uncons {y} [ rxy ]⁺   = y , rxy , ε refl
plus-uncons     (_◅⁺_ {y = w} rxw p) = w , rxw , plus→star p

plus-last : ∀ {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y : A}
          → Plus R x y → Σ[ z ꞉ A ] (Star R x z × R z y)
plus-last {x} [ rxy ]⁺   = x , ε refl , rxy
plus-last     (rxw ◅⁺ p) =
  let (z , s , r) = plus-last p in
  z , rxw ◅ s , r

plus-trans-star : Plus R x y → Star R y z → Plus R x z
plus-trans-star {R} {x} pxy (ε e)       = subst (Plus R x) e pxy
plus-trans-star         pxy (ryw ◅ swz) = plus-trans-star (pxy ◅⁺∷ ryw) swz

_◅⋆∷_ : Star R x y → R y z → Plus R x z
_◅⋆∷_ {R} {z} (ε e) ryz = [ subst (λ q → R q z) (e ⁻¹) ryz ]⁺
(rxw ◅ swy) ◅⋆∷ ryz     = rxw ◅⁺ (swy ◅⋆∷ ryz)

-- TODO generalize

plus-fold1 : Trans R → Plus R x y → R x y
plus-fold1 tr [ rxy ]⁺     = rxy
plus-fold1 tr (rxw ◅⁺ pwy) = tr ._∙_ rxw (plus-fold1 tr pwy)

wf→acyclic+ : ∀ {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ}
            → is-wf R
            → ∀ x
            → ¬ Plus R x x
wf→acyclic+ {R = R} wf x p =
  let (y , r , s) = plus-uncons p in
  wf→acyclic wf x x y (ε refl) r s
