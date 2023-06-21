{-# OPTIONS --safe #-}
module Data.Unit.Properties where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Unit.Base

private variable
  ℓ : Level
  A : Type ℓ

opaque
  unfolding is-of-hlevel
  is-contr→equiv-⊤ : is-contr A → A ≃ Lift ℓ ⊤
  is-contr→equiv-⊤ A-ctr .fst _ = lift tt
  is-contr→equiv-⊤ A-ctr .snd .equiv-proof (lift tt)
    = (A-ctr .fst , refl) , λ { (a , p) i → A-ctr .snd a i , refl }
