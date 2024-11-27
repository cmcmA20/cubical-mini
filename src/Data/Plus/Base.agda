{-# OPTIONS --safe #-}
module Data.Plus.Base where

open import Foundations.Base

-- aka transitive closure
data Plus {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (R : A → A → 𝒰 ℓ) : A → A → 𝒰 (ℓᵃ ⊔ ℓ) where
  [_]⁺ : ∀ {x y} → R x y → Plus R x y
  _◅⁺_ : ∀ {x y z} → R x y → Plus R y z → Plus R x z

private variable
  ℓ : Level
  A B : 𝒰 ℓ
  R S : A → A → 𝒰 ℓ
  x x′ y y′ z : A

plus-trans : Plus R x y → Plus R y z → Plus R x z
plus-trans [ xy ]⁺     pyz = xy ◅⁺ pyz
plus-trans (xw ◅⁺ pwy) pyz = xw ◅⁺ plus-trans pwy pyz

_◅⁺∷_ : Plus R x y → R y z → Plus R x z
pxy ◅⁺∷ ryz = plus-trans pxy [ ryz ]⁺

instance
  Trans-Plus : Trans (Plus R)
  Trans-Plus ._∙_ = plus-trans

plus-map : {f : A → B}
         → (∀ {a b} → R a b → S (f a) (f b))
         → Plus R x y → Plus S (f x) (f y)
plus-map fp [ xy ]⁺     = [ fp xy ]⁺
plus-map fp (xw ◅⁺ pwy) = fp xw ◅⁺ plus-map fp pwy
