{-# OPTIONS --safe #-}
module Data.Star.Properties where

open import Foundations.Base

open import Data.Empty.Base
open import Data.Acc.Base
open import Data.Acc.Properties
open import Data.Sum.Base

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Star.Base
open import Data.Sum.Base

private variable
  ℓ ℓa : Level
  A B : 𝒰 ℓ
  R S : A → A → 𝒰 ℓ
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

star-last : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y : A}
          → Star R x y → (x ＝ y) ⊎ (Σ[ z ꞉ A ] (Star R x z × R z y))
star-last             (ε e)   = inl e
star-last {R} {x} {y} (r ◅ s) =
  [ (λ e                     → inr (x , ε refl , subst (R x) e r))
  , (λ where (z , swz , rzy) → inr (z , r ◅ swz , rzy)) ]ᵤ
    (star-last s)

-- generalizes wf→irrefl and wf→asym
wf→acyclic : ∀ {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ}
           → is-wf R
           → ∀ x y z
           → Star R x y → R y z → Star R z x
           → ⊥
wf→acyclic {R} wf =
  to-induction wf (λ x → ∀ y z → Star R x y → R y z → Star R z x → ⊥)
   λ x ih y z sxy ryz →
      [ (λ e →
           ih y (subst (R y) e ryz) y z (ε refl)    ryz (subst (λ q → Star R q y) (e ⁻¹) sxy))
      , (λ (w , swz , rwx) →
           ih w                rwx  y z (rwx ◅ sxy) ryz                                 swz)
      ]ᵤ ∘ star-last
