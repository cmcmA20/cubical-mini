{-# OPTIONS --safe --erased-cubical #-}
module Cubical.Data.Empty.Base where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level

data ⊥ : Type₀ where

⊥* : Type ℓ
⊥* = Lift ⊥

rec : {A : Type ℓ} → @0 ⊥ → A
rec ()

rec* : {A : Type ℓ} → @0 ⊥* {ℓ = ℓ'} → A
rec* ()

elim : {A : ⊥ → Type ℓ} → (@0 x : ⊥) → A x
elim ()
