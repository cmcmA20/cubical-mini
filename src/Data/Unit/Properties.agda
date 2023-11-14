{-# OPTIONS --safe #-}
module Data.Unit.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Unit.Base

private variable
  ℓ : Level
  A : Type ℓ

universal : (⊤ → A) ≃ A
universal .fst = _$ tt
universal .snd .equiv-proof = strict-contr-fibres (λ x _ → x)

opaque
  unfolding is-of-hlevel
  is-contr→equiv-⊤ : is-contr A → A ≃ ⊤
  is-contr→equiv-⊤ A-ctr .fst _ = tt
  is-contr→equiv-⊤ A-ctr .snd .equiv-proof tt
    = (A-ctr .fst , refl) , λ { (a , _) i → A-ctr .snd a i , refl }
