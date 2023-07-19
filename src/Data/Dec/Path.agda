{-# OPTIONS --safe #-}
module Data.Dec.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Data.Empty.Base
open import Data.Empty.Instances.HLevel
open import Data.Sum.Path

open import Data.Dec.Base public

private variable
  ℓ : Level
  A : Type ℓ

dec-as-sum : Dec A ≃ ((¬ A) ⊎ A)
dec-as-sum = iso→equiv helper where
  helper : Iso _ _
  helper .fst (yes a) = inr  a
  helper .fst (no ¬a) = inl ¬a
  helper .snd .is-iso.inv (inl ¬a) = no ¬a
  helper .snd .is-iso.inv (inr  a) = yes a
  helper .snd .is-iso.rinv (inl ¬a) = refl
  helper .snd .is-iso.rinv (inr  a) = refl
  helper .snd .is-iso.linv (no ¬a) = refl
  helper .snd .is-iso.linv (yes a) = refl

opaque
  unfolding is-of-hlevel
  dec-contr : is-contr A → is-contr (Dec A)
  dec-contr (a , _) .fst = yes a
  dec-contr (a , p) .snd (no ¬a)  = absurd (¬a a)
  dec-contr (a , p) .snd (yes a′) = ap yes (p a′)

dec-is-of-hlevel : (n : HLevel) → is-of-hlevel n A → is-of-hlevel n (Dec A)
dec-is-of-hlevel 0 = dec-contr
dec-is-of-hlevel 1 A-hl =
  is-of-hlevel-≃ 1 dec-as-sum (disjoint-⊎-is-prop hlevel! A-hl (λ f → f .fst (f .snd)))
dec-is-of-hlevel (suc (suc n)) A-hl =
  is-of-hlevel-≃ (suc (suc n)) dec-as-sum (⊎-is-of-hlevel n hlevel! A-hl)
