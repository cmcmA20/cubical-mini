{-# OPTIONS --safe #-}
module Cubical.Data.Maybe.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat.Base
open import Cubical.Data.Maybe.Base
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.SumFin.Base
open import Cubical.HITs.PropositionalTruncation as ∥∥

open import Cubical.Interface.DecEq
open import Cubical.Interface.Finite
open import Cubical.Interface.HLevels
open import Cubical.Interface.Show

open DecEq ⦃ ... ⦄
open Finite ⦃ ... ⦄
open IsOfHLevel ⦃ ... ⦄
open Show ⦃ ... ⦄

private variable
  ℓ : Level
  A : Type ℓ
  n : HLevel

instance
  DecEqMaybe : ⦃ DecEq A ⦄ → DecEq (Maybe A)
  DecEq._≟_ DecEqMaybe = discreteMaybe _≟_


instance
  FiniteMaybe : ⦃ Finite A ⦄ → Finite (Maybe A)
  Finite.isFinite (FiniteMaybe {A = A} ⦃ Af ⦄) = suc m , ∥∥.map (isoToEquiv ∘ helper) (Af .isFinite .snd)
    where
    m = Af .isFinite .fst
    helper : (e : _) → Iso (Maybe A) (⊤ ⊎ Fin m)
    Iso.fun (helper e) nothing  = inl tt
    Iso.fun (helper e) (just x) = inr (e .fst x)
    Iso.inv (helper e) (inl _)  = nothing
    Iso.inv (helper e) (inr x)  = just (invEquiv e .fst x)
    Iso.rightInv (helper e) (inl _) = refl
    Iso.rightInv (helper e) (inr x) = cong inr (cong (λ t → t .fst x) (invEquiv-is-linv e))
    Iso.leftInv (helper e) nothing = refl
    Iso.leftInv (helper e) (just x) = cong just (cong (λ t → t .fst x) (invEquiv-is-rinv e))


instance
  IsOfHLevelMaybe : ⦃ IsOfHLevel (suc (suc n)) A ⦄
                  → IsOfHLevel (suc (suc n)) (Maybe A)
  IsOfHLevel.iohl (IsOfHLevelMaybe ⦃ Al ⦄) = isOfHLevelMaybe _ (Al .iohl)


instance
  ShowMaybe : ⦃ Show A ⦄ → Show (Maybe A)
  Show.show ShowMaybe nothing  = "nothing"
  Show.show ShowMaybe (just x) = "just " ++ show x
