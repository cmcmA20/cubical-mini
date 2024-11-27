{-# OPTIONS --safe #-}
module Data.Star.Properties where

open import Foundations.Base
open import Foundations.Path

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

star-cast-l-refl : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y : A}
                 → (sxy : Star R x y)
                 → star-cast-l refl sxy ＝ sxy
star-cast-l-refl (ε e) = ap ε (∙-id-o e)
star-cast-l-refl {R} {x} (r ◅ sxy) = ap (_◅ sxy) (subst-refl {B = R x} r)

star-trans-id-l : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y : A}
                → (sxy : Star R x y)
                → refl ∙ sxy ＝ sxy
star-trans-id-l = star-cast-l-refl

star-trans-id-r : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y : A}
                → (sxy : Star R x y)
                → sxy ∙ refl ＝ sxy
star-trans-id-r (ε e)       = ap ε (∙-id-i e)
star-trans-id-r (rxw ◅ swy) = ap (rxw ◅_) (star-trans-id-r swy)

star-trans-assoc : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y z w : A}
                 → (sxy : Star R x y) (syz : Star R y z) (szw : Star R z w)
                 → (sxy ∙ syz) ∙ szw ＝ sxy ∙ (syz ∙ szw)
star-trans-assoc {R} {z} (ε e)     syz szw =
  Jₚ (λ a ea → (saz : Star R a z)
             → star-trans (star-cast-l (ea ⁻¹) saz) szw ＝
               star-cast-l (ea ⁻¹) (star-trans saz szw))
     (λ sxz →   ap (λ q → star-trans q szw) (star-cast-l-refl sxz)
              ∙ star-cast-l-refl (sxz ∙ szw) ⁻¹)
     e syz
star-trans-assoc (r ◅ sxy) syz szw =
  ap (r ◅_) (star-trans-assoc sxy syz szw)

star-trans-len
  : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y z : A}
  → (sxy : Star R x y) (syz : Star R y z)
  → star-len (sxy ∙ syz) ＝ star-len sxy + star-len syz
star-trans-len (ε u)     (ε v)     = refl
star-trans-len (ε u)     (v ◅ syz) = refl
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

star-foldr-emp : {A : 𝒰 ℓa} {R S : A → A → 𝒰 ℓ} {x : A}
               → (re : ∀ {x} → S x x)
               → {tr : ∀ {x y z} → R x y → S y z → S x z}
               → star-foldr re tr (the (Star R x x) refl) ＝ re {x}
star-foldr-emp {S} {x} re = subst-refl {B = S x} re

star-foldr-trans-morph : {A : 𝒰 ℓa} {R S : A → A → 𝒰 ℓ} {x y z : A}
                       → (re : ∀ {x} → S x x)
                       → (mf : ∀ {x y} → R x y → S x y)
                       → (tr : ∀ {x y z} → S x y → S y z → S x z)
                       → (∀ {x y} {s : S x y} → tr re s ＝ s)
                       → (∀ {x y z w} {a : S x y} {b : S y z} {c : S z w} → tr a (tr b c) ＝ tr (tr a b) c)
                       → (sxy : Star R x y) (syz : Star R y z)
                       → star-foldr re (tr ∘ mf) (sxy ∙ syz) ＝
                         tr (star-foldr re (tr ∘ mf) sxy) (star-foldr re (tr ∘ mf) syz)
star-foldr-trans-morph {R} {S} {x} {z} re mf tr trlu tras (ε e)       syz =
  Jₚ (λ a ea → (saz : Star R a z)
             → star-foldr re (tr ∘ mf) (star-cast-l (ea ⁻¹) saz) ＝
               tr (subst (S x) ea re) (star-foldr re (tr ∘ mf) saz))
     (λ sxz →   ap (star-foldr re (tr ∘ mf)) (star-cast-l-refl sxz)
              ∙ trlu ⁻¹
              ∙ ap (λ q → tr q (star-foldr re (tr ∘ mf) sxz))
                   (star-foldr-emp (λ {x} → re {x}) {tr = tr ∘ mf} ⁻¹))
     e syz
star-foldr-trans-morph re mf tr trlu tras (rxw ◅ swy) syz =
    ap (tr (mf rxw)) (star-foldr-trans-morph re mf tr trlu tras swy syz) ∙ tras

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
