{-# OPTIONS --safe #-}
module Data.Star.Base where

open import Foundations.Base

-- aka reflexive-transitive closure
data Star {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : A → A → 𝒰 (ℓᵃ ⊔ ℓ) where
  ε   : ∀ {x y} → x ＝ y → Star R x y
  _◅_ : ∀ {x y z} → R x y → Star R y z → Star R x z

record Substar {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : 𝒰 (ℓᵃ ⊔ ℓ) where
  constructor sst
  field
    from : A
    to   : A
    path : Star R from to

private variable
  ℓ : Level
  A B : 𝒰 ℓ
  R S : A → A → 𝒰 ℓ
  x x′ y y′ z : A

star-sng : R x y → Star R x y
star-sng rxy = rxy ◅ ε refl

star-cast : (p : x ＝ x′) (q : y ＝ y′)
          → Star R x y → Star R x′ y′
star-cast     p q (ε e)   = ε (p ⁻¹ ∙ e ∙ q)
star-cast {R} p q (e ◅ s) = subst (λ φ → R φ _) p e ◅ star-cast refl q s

star-cast-l : (p : x ＝ x′)
            → Star R x y → Star R x′ y
star-cast-l     p (ε e)   = ε (p ⁻¹ ∙ e)
star-cast-l {R} p (e ◅ s) = subst (λ φ → R φ _) p e ◅ s

star-cast-r : (p : y ＝ y′)
            → Star R x y → Star R x y′
star-cast-r p (ε e)   = ε (e ∙ p)
star-cast-r p (e ◅ s) = e ◅ star-cast-r p s

star-trans : Star R x y → Star R y z → Star R x z
star-trans (ε e)      syz = star-cast-l (e ⁻¹) syz
star-trans (xw ◅ swy) syz = xw ◅ star-trans swy syz

_◅+_ : Star R x y → R y z → Star R x z
sxy ◅+ ryz = star-trans sxy (star-sng ryz)

instance
  Refl-Star : Refl (Star R)
  Refl-Star .refl = ε refl

  Trans-Star : Trans (Star R)
  Trans-Star ._∙_ = star-trans

star-map : {f : A → B}
         → (∀ {a b} → R a b → S (f a) (f b))
         → Star R x y → Star S (f x) (f y)
star-map {f} fp (ε e)      = ε (ap f e)
star-map     fp (xw ◅ swy) = fp xw ◅ star-map fp swy

-- recursor
-- TODO generalize ?
star-foldr : (∀ {x y} → x ＝ y → S x y)
           → (∀ {x y z} → R x y → S y z → S x z)
           → Star R x y → S x y
star-foldr re tr (ε e)       = re e
star-foldr re tr (rxw ◅ swy) = tr rxw (star-foldr re tr swy)

star-foldrm : (∀ {x y} → x ＝ y → S x y)
            → (∀ {x y} → R x y → S x y)
            → (pl : ∀ {x y z} → S x y → S y z → S x z)
            → Star R x y → S x y
star-foldrm re mf pl = star-foldr re (pl ∘ mf)

-- TODO
-- star-foldl : (∀ {a} → S a a)
--            → (∀ {a b c} → S a b → R b c → S a c)
--            → Star R x y → S x y
