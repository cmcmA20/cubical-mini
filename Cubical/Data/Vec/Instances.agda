{-# OPTIONS --safe #-}
module Cubical.Data.Vec.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base
open import Cubical.Data.Vec.Base
open import Cubical.Data.Vec.Properties

open import Cubical.Interface.DecEq
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show renaming (_++_ to _++ₛ_)

open DecEq ⦃ ... ⦄
open IsOfHLevel ⦃ ... ⦄
open Show ⦃ ... ⦄

private variable
  ℓ : Level
  A : Type ℓ
  n : ℕ
  h : HLevel

instance
  DecEqVec : ⦃ DecEq A ⦄ → DecEq (Vec A n)
  DecEq._≟_ DecEqVec = VecPath.discreteA→discreteVecA _≟_ _

instance
  IsOfHLevelVec : ⦃ IsOfHLevel (suc (suc h))       A ⦄
                 →   IsOfHLevel (suc (suc h)) (Vec A n)
  IsOfHLevel.iohl (IsOfHLevelVec ⦃ Al ⦄) = VecPath.isOfHLevelVec _ _ (Al .iohl)

instance
  ShowVec : ⦃ Show A ⦄ → Show (Vec A n)
  Show.show ShowVec xs = foldrₗ _++ₛ_ "" $ intersperse ", " $ mapₗ show (toList xs)
    where open import Cubical.Data.List.Base renaming (map to mapₗ; foldr to foldrₗ)
          toList : Vec A n → List A
          toList []       = []
          toList (x ∷ xs) = x ∷ toList xs
