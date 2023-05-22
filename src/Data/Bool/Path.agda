{-# OPTIONS --safe #-}
module Data.Bool.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Sum
open import Data.Unit

open import Meta.Reflection.HLevel

open import Structures.Negation

open import Data.Bool.Base public

bool-as-sum : Bool ≃ (⊤ ⊎ ⊤)
bool-as-sum = Iso→Equiv 𝔯
  where
  𝔯 : Iso _ _
  𝔯 .fst false = inj-l tt
  𝔯 .fst true  = inj-r tt
  𝔯 .snd .is-iso.inv (inj-l _) = false
  𝔯 .snd .is-iso.inv (inj-r _) = true
  𝔯 .snd .is-iso.rinv (inj-l _) = refl
  𝔯 .snd .is-iso.rinv (inj-r _) = refl
  𝔯 .snd .is-iso.linv false = refl
  𝔯 .snd .is-iso.linv true  = refl

false≠true : ¬ false ＝ true
false≠true = ⊎-disjoint ∘ ap (bool-as-sum .fst)

Bool-is-set : is-set Bool
Bool-is-set = is-of-hlevel-≃ 2 bool-as-sum hlevel!
