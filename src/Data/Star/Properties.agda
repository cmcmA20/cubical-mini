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
open import Data.Star.Base as Star
open import Data.Sum.Base

private variable
  ℓ ℓ′ ℓ″ ℓa : Level
  A B : 𝒰 ℓ
  R : A → A → 𝒰 ℓ
  S : A → A → 𝒰 ℓ′
  x y z : A

star-len : Star R x y → ℕ
star-len (ε _)   = 0
star-len (_ ◅ s) = suc (star-len s)

star-cast-l-refl : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y : A}
                 → (sxy : Star R x y)
                 → star-cast-l refl sxy ＝ sxy
star-cast-l-refl (ε e) = ap ε (∙-id-o e)
star-cast-l-refl {R} {x} (r ◅ sxy) = ap (_◅ sxy) (subst-refl {B = R x} r)

star-trans-sng : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {x y z : A}
               → (rxy : R x y) (syz : Star R y z)
               → rxy ◅ syz ＝ star-sng rxy ∙ syz
star-trans-sng rxy syz = ap (rxy ◅_) (star-cast-l-refl syz ⁻¹)

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

elim-◅+-concat : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {P : ∀ {x y} → Star R x y → 𝒰 ℓ″}
               → ({x y z : A} (sxy : Star R x y) → P sxy → (ryz : R y z) → P (sxy ◅+ ryz))
               → {x y z : A} (sxy : Star R x y) (syz : Star R y z) → P sxy → P (sxy ∙ syz)
elim-◅+-concat {P} pc sxy (ε eq)   pxy =
  Jₚ (λ z ez → P (sxy ∙ ε ez))
     (subst P (star-trans-id-r sxy ⁻¹) pxy)
     eq
elim-◅+-concat {P} pc sxy (ryw ◅ swz) pxy =
  subst P
        (  star-trans-assoc sxy (star-sng ryw) swz
         ∙ ap (sxy ∙_) (star-trans-sng ryw swz ⁻¹)) $
  elim-◅+-concat
    pc
    (sxy ◅+ ryw) swz (pc _ pxy ryw)

elim-◅+ : {P : ∀ {x y} → Star R x y → 𝒰 ℓ″}
        → (∀ {x y} (e : x ＝ y) → P (ε e))
        → (∀ {x y z} (sxy : Star R x y) → P sxy → (ryz : R y z) → P (sxy ◅+ ryz))
        → ∀ {x y} (sxy : Star R x y) → P sxy
elim-◅+ {R} {P} pe pc sxy =
  subst P (star-cast-l-refl sxy) $
  elim-◅+-concat pc refl sxy (pe refl)

elim-◅+J : {P : ∀ {x y} → Star R x y → 𝒰 ℓ″}
         → (∀ {x} → P (ε (λ _ → x)))
         → (∀ {x y z} (sxy : Star R x y) → P sxy → (ryz : R y z) → P (sxy ◅+ ryz))
         → ∀ {x y} (sxy : Star R x y) → P sxy
elim-◅+J {R} {P} pe pc sxy =
  subst P (star-cast-l-refl sxy) $
  elim-◅+-concat pc refl sxy pe

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

star-rec-emp : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {S : A → A → 𝒰 ℓ′}
               → (re : ∀ {x y} → x ＝ y → S x y)
               → {tr : ∀ {x y z} → R x y → S y z → S x z}
               → {x : A}
               → Star.rec re tr (the (Star R x x) refl) ＝ re (refl)
star-rec-emp {S} re {x} = refl

star-foldrm-trans : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {S : A → A → 𝒰 ℓ′} {x y z : A}
                  → (re : ∀ {x y} → x ＝ y → S x y)
                  → (mf : ∀ {x y} → R x y → S x y)
                  → (pl : ∀ {x y z} → S x y → S y z → S x z)
                  → (∀ {x y} {s : S x y} → pl (re refl) s ＝ s)
                  → (∀ {x y z w} {a : S x y} {b : S y z} {c : S z w} → pl a (pl b c) ＝ pl (pl a b) c)
                  → (sxy : Star R x y) (syz : Star R y z)
                  → star-foldrm re mf pl (sxy ∙ syz) ＝
                    pl (star-foldrm re mf pl sxy)
                       (star-foldrm re mf pl syz)
star-foldrm-trans {R} {S} {x} {z} re mf pl pllu plas (ε e)       syz =
  Jₚ (λ a ea → (saz : Star R a z)
               → star-foldrm re mf pl (star-cast-l (ea ⁻¹) saz) ＝
                 pl (re ea) (star-foldrm re mf pl saz))
     (λ sxz → ap (star-foldrm re mf pl) (star-cast-l-refl sxz)
              ∙ pllu ⁻¹
              ∙ ap (λ q → pl q (star-foldrm re mf pl sxz))
                   (star-rec-emp (λ {x} → re {x}) {tr = pl ∘ mf} ⁻¹))
     e syz
star-foldrm-trans                 re mf pl pllu plas (rxw ◅ swy) syz =
  ap (pl (mf rxw)) (star-foldrm-trans re mf pl pllu plas swy syz) ∙ plas

star-foldrm-◅+ : {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ} {S : A → A → 𝒰 ℓ′} {x y z : A}
               → (re : ∀ {x y} → x ＝ y → S x y)
               → (mf : ∀ {x y} → R x y → S x y)
               → (pl : ∀ {x y z} → S x y → S y z → S x z)
               → (∀ {x y} {s : S x y} → pl (re refl) s ＝ s)
               → (∀ {x y} {s : S x y} → pl s (re refl) ＝ s)
               → (∀ {x y z w} {a : S x y} {b : S y z} {c : S z w} → pl a (pl b c) ＝ pl (pl a b) c)
               → (sxy : Star R x y) (ryz : R y z)
               → star-foldrm re mf pl (sxy ◅+ ryz) ＝
                 pl (star-foldrm re mf pl sxy) (mf ryz)
star-foldrm-◅+ re mf pl pllu plru plas sxy ryz =
    star-foldrm-trans re mf pl pllu plas sxy (star-sng ryz)
  ∙ ap (pl (star-foldrm re mf pl sxy)) plru

-- generalizes wf→irrefl and wf→asym
wf→acyclic : ∀ {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ}
           → is-wf R
           → ∀ x y z
           → Star R x y → R y z → Star R z x
           → ⊥
wf→acyclic {R} wf =
  to-induction wf (λ x → ∀ y z → Star R x y → R y z → Star R z x → ⊥)
   λ x ih y z sxy ryz →
      [ (λ z=x →
           ih y (subst (R y) z=x ryz) y z (ε refl)    ryz (subst (λ q → Star R q y) (z=x ⁻¹) sxy))
      , (λ (w , swz , rwx) →
           ih w                  rwx  y z (rwx ◅ sxy) ryz                                    swz)
      ]ᵤ ∘ star-last

-- TODO reorder vars to match wf→acyclic
noeth→acyclic : ∀ {A : 𝒰 ℓa} {R : A → A → 𝒰 ℓ}
           → is-noeth R
           → ∀ x y z
           → Star R y x → R z y → Star R x z
           → ⊥
noeth→acyclic {R} nth =
  to-ninduction nth (λ x → ∀ y z → Star R y x → R z y → Star R x z → ⊥)
   λ x ih y z syx rzy →
   λ where
       (ε x=z) →
         ih y (subst (λ q → R q y) (x=z ⁻¹) rzy) y z (ε refl)     rzy (subst (Star R y) x=z syx)
       (rxw ◅ swz) →
         ih _  rxw                               y z (syx ◅+ rxw) rzy                       swz
