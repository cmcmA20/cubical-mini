{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Bind where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Bind

open import Data.Maybe.Base
open import Data.Maybe.Instances.Idiom public

open Bind ⦃ ... ⦄
open Lawful-Bind ⦃ ... ⦄

instance
  Bind-Maybe : Bind (eff Maybe)
  Bind-Maybe ._>>=_ (just x) k = k x
  Bind-Maybe ._>>=_ nothing  _ = nothing

  Lawful-Bind-Maybe : Lawful-Bind (eff Maybe)
  Lawful-Bind-Maybe .>>=-id-l = refl
  Lawful-Bind-Maybe .>>=-id-r {mx = just x} = refl
  Lawful-Bind-Maybe .>>=-id-r {mx = nothing} = refl
  Lawful-Bind-Maybe .>>=-assoc {mx = just x} = refl
  Lawful-Bind-Maybe .>>=-assoc {mx = nothing} = refl
  Lawful-Bind-Maybe .<*>->>= {mf = just f} {just x} = refl
  Lawful-Bind-Maybe .<*>->>= {mf = just f} {(nothing)} = refl
  Lawful-Bind-Maybe .<*>->>= {mf = nothing} = refl
