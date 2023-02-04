-- NOTE: the contents of this module should be accessed via `IO`.

{-# OPTIONS --erased-cubical #-}

module Cubical.IO.Primitive where

open import Cubical.Foundations.Prelude

------------------------------------------------------------------------
-- The IO monad

open import Agda.Builtin.IO public using (IO)

infixl 1 _>>=_

postulate
  pure : ∀ {ℓᵃ} {A : Type ℓᵃ} → A → IO A
  _>>=_  : ∀ {ℓᵃ ℓᵇ} {A : Type ℓᵃ} {B : Type ℓᵇ} → IO A → (A → IO B) → IO B

{-# COMPILE GHC pure = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}
{-# COMPILE UHC pure = \_ _ x -> UHC.Agda.Builtins.primReturn x #-}
{-# COMPILE UHC _>>=_  = \_ _ _ _ x y -> UHC.Agda.Builtins.primBind x y #-}
