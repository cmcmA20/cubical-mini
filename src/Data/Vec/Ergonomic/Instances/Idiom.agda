{-# OPTIONS --safe #-}
module Data.Vec.Ergonomic.Instances.Idiom where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom

open import Data.Vec.Ergonomic.Base
open import Data.Vec.Ergonomic.Instances.Map public

private variable
  ℓ : Level
  A : Type ℓ

instance
  Idiom-Vec : ∀{n} → Idiom (eff λ T → Vec T n)
  Idiom-Vec .pure x = replicate _ x
  Idiom-Vec {0} ._<*>_ _ _ = _
  Idiom-Vec {1} ._<*>_ f x = f x
  Idiom-Vec {suc (suc _)} ._<*>_ (f , fs) (x , xs) =
    f x , Idiom-Vec ._<*>_ fs xs
