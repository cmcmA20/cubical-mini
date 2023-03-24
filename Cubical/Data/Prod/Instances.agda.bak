{-# OPTIONS --safe #-}
module Cubical.Data.Prod.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat.Base
open import Cubical.Data.Prod.Base
open import Cubical.Data.Prod.Properties
open import Cubical.Data.Sigma using () renaming (_×_ to _×Σ_)
open import Cubical.Data.SumFin.Base
open import Cubical.Data.SumFin.Properties
open import Cubical.Truncation.Propositional as ∥∥

open import Cubical.Interface.DecEq
open import Cubical.Interface.Finite
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

open DecEq ⦃ ... ⦄
open Finite ⦃ ... ⦄
open IsOfHLevel ⦃ ... ⦄
open Show ⦃ ... ⦄

private variable
  ℓ ℓ′ : Level
  n : HLevel
  A : Type ℓ
  B : Type ℓ′

instance
  DecEq× : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (A × B)
  DecEq._≟_ DecEq× (xᵃ , xᵇ) (yᵃ , yᵇ) with xᵃ ≟ yᵃ | xᵇ ≟ yᵇ
  ... | yes xᵃ≡yᵃ | yes xᵇ≡yᵇ = yes (cong₂ _,_ xᵃ≡yᵃ xᵇ≡yᵇ)
  ... | yes xᵃ≡yᵃ | no  xᵇ≢yᵇ = no λ p → xᵇ≢yᵇ (cong proj₂ p)
  ... | no  xᵃ≢yᵃ | yes xᵇ≡yᵇ = no λ p → xᵃ≢yᵃ (cong proj₁ p)
  ... | no  xᵃ≢yᵃ | no  xᵇ≢yᵇ = no λ p → xᵃ≢yᵃ (cong proj₁ p)
  -- FIXME should probably match sequentially


instance
  Finite× : {ℓ ℓ′ : Level} → {A : Type ℓ} → {B : Type ℓ′} → ⦃ Finite A ⦄ → ⦃ Finite B ⦄ → Finite (A × B)
  Finite.isFinite (Finite× {A = A} {B = B} ⦃ Af ⦄ ⦃ Bf ⦄) =
    let
      m = Af .isFinite .fst
      k = Bf .isFinite .fst
      prodEquivalence : A ≃ Fin m
                      → B ≃ Fin k
                      → A × B ≃ Fin (m · k)
      prodEquivalence Ae Be =
        A     ×  B     ≃⟨ ×-≃ Ae Be    ⟩
        Fin m ×  Fin k ≃⟨ A×B≃A×ΣB     ⟩
        Fin m ×Σ Fin k ≃⟨ SumFin×≃ m k ⟩
        Fin (m · k)    ■
    in m · k , ∥∥.map2 prodEquivalence (Af .isFinite .snd) (Bf .isFinite .snd)


instance
  @0 IsOfHLevel× : ⦃ IsOfHLevel n A ⦄ → ⦃ IsOfHLevel n B ⦄
                 → IsOfHLevel n (A × B)
  IsOfHLevel.iohl IsOfHLevel× = isOfHLevelProd _ iohl iohl


instance
  Show× : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A × B)
  Show.show Show× (a , b) = show a ++ (" , " ++ show b)
