{-# OPTIONS --safe #-}
module Order.Category where

open import Cat.Prelude

open import Order.Base

poset→precategory : ∀ {o ℓ} → Poset o ℓ → Precategory o ℓ
poset→precategory P = cat where
  open Poset P
  open Precategory
  cat : Precategory _ _
  cat .Ob  = P .Ob
  cat .Hom = _≤_
  cat .id  = ≤-refl
  cat ._∘_ = flip ≤-trans
  cat .id-r _      = prop!
  cat .id-l _      = prop!
  cat .assoc _ _ _ = prop!
  cat .Hom-set _ _ = hlevel!

-- TODO
-- open Functor
-- Posets↪Strict-cats : ∀ {ℓ ℓ'} → Functor (Posets ℓ ℓ') (Strict-cats ℓ ℓ')
-- Posets↪Strict-cats .F₀ P = poset→category P , Poset.Ob-is-set P
-- Posets↪Strict-cats .F₁ f .F₀ = f .hom
-- Posets↪Strict-cats .F₁ f .F₁ = f .pres-≤
-- Posets↪Strict-cats .F₁ {y = y} f .F-id    = Poset.≤-thin y _ _
-- Posets↪Strict-cats .F₁ {y = y} f .F-∘ g h = Poset.≤-thin y _ _
-- Posets↪Strict-cats .F-id    = Functor-path (λ _ → refl) λ _ → refl
-- Posets↪Strict-cats .F-∘ f g = Functor-path (λ _ → refl) λ _ → refl
