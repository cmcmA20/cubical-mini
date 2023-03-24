{-# OPTIONS --safe #-}
module Cubical.Instances.DecEq.Data.Prod where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Prod.Base

open import Cubical.Instances.DecEq.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

instance
  DecEq× : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (A × B)
  DecEq._≟_ DecEq× (xᵃ , xᵇ) (yᵃ , yᵇ) with xᵃ ≟ yᵃ | xᵇ ≟ yᵇ
  ... | yes xᵃ≡yᵃ | yes xᵇ≡yᵇ = yes (cong₂ _,_ xᵃ≡yᵃ xᵇ≡yᵇ)
  ... | yes xᵃ≡yᵃ | no  xᵇ≢yᵇ = no λ p → xᵇ≢yᵇ (cong proj₂ p)
  ... | no  xᵃ≢yᵃ | yes xᵇ≡yᵇ = no λ p → xᵃ≢yᵃ (cong proj₁ p)
  ... | no  xᵃ≢yᵃ | no  xᵇ≢yᵇ = no λ p → xᵃ≢yᵃ (cong proj₁ p)
  -- TODO should probably match sequentially?
