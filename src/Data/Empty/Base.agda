{-# OPTIONS --safe #-}
module Data.Empty.Base where

open import Foundations.Type

data ⊥ : Type where

private variable ℓ ℓ′ : Level

rec : {@0 A : Type ℓ} → @0 ⊥ → A
rec ()

elim : {@0 A : ⊥ → Type ℓ} → (@0 x : ⊥) → A x
elim ()


⊥* : Type ℓ
⊥* {ℓ} = Lift ℓ ⊥

rec* : {@0 A : Type ℓ′} → @0 ⊥* {ℓ} → A
rec* ()

elim* : {@0 A : ⊥* {ℓ} → Type ℓ′} → (@0 x : ⊥*) → A x
elim* ()


data ⊥ω : Typeω where

⊥→⊥ω : ⊥ → ⊥ω
⊥→⊥ω ()

recω : {@0 A : Typeω} → @0 ⊥ω → A
recω ()

elimω : {@0 A : ⊥ω → Typeω} → (@0 x : ⊥ω) → A x
elimω ()
