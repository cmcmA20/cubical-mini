{-# OPTIONS --safe #-}
module Data.Bool.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.HLevel

open import Data.Empty.Base
open import Data.Sum
open import Data.Unit

open import Data.Bool.Base public

bool-as-sum : Bool ≃ (⊤ ⊎ ⊤)
bool-as-sum = iso→equiv 𝔯
  where
  𝔯 : Iso _ _
  𝔯 .fst false = inl tt
  𝔯 .fst true  = inr tt
  𝔯 .snd .is-iso.inv (inl _) = false
  𝔯 .snd .is-iso.inv (inr _) = true
  𝔯 .snd .is-iso.rinv (inl _) = refl
  𝔯 .snd .is-iso.rinv (inr _) = refl
  𝔯 .snd .is-iso.linv false = refl
  𝔯 .snd .is-iso.linv true  = refl

false≠true : ¬ false ＝ true
false≠true = ⊎-disjoint ∘ ap (bool-as-sum .fst)

true≠false : ¬ true ＝ false
true≠false = false≠true ∘ sym

-- do not use this directly, there is a derived instance
Bool-is-set : is-set Bool
Bool-is-set = is-of-hlevel-≃ 2 bool-as-sum hlevel!
