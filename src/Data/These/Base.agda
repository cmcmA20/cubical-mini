{-# OPTIONS --safe #-}
module Data.These.Base where

open import Foundations.Base
open import Data.Bool.Base
  using (Bool; So; _or_; oh; true; false; not)
import Data.Reflects.Base as Reflects
open Reflects using (ofʸ; ofⁿ)
open import Data.Maybe.Base using (Maybe; just; nothing)

data These {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  this  : A → These A B
  that  : B → These A B
  these : A → B → These A B

private variable
  ℓ ℓ′ ℓ″ ℓᵃ ℓᵇ ℓᶜ ℓᵈ : Level
  A : Type ℓᵃ
  B : Type ℓᵇ
  C : Type ℓᶜ
  D : Type ℓᵈ

elim : {C : These A B → Type ℓ′}
     → ((a : A) → C (this a))
     → ((b : B) → C (that b))
     → ((a : A) → (b : B) → C (these a b))
     → (d : These A B) → C d
elim l r lr (this a)    = l a
elim l r lr (that b)    = r b
elim l r lr (these a b) = lr a b

rec : (A → C) → (B → C) → (A → B → C) → These A B → C
rec = elim

dmap : (A → B) → (C → D) → These A C → These B D
dmap f g (this a)    = this (f a)
dmap f g (that b)    = that (g b)
dmap f g (these a b) = these (f a) (g b)

map-l : (A → B) → These A C → These B C
map-l f = dmap f id

map-r : (B → C) → These A B → These A C
map-r = dmap id

swap : These A B → These B A
swap = rec that this (flip these)

fromMaybe2 : Maybe A → Maybe B → Maybe (These A B)
fromMaybe2 (just a) (just b) = just (these a b)
fromMaybe2 (just a)  nothing = just (this a)
fromMaybe2  nothing (just b) = just (that b)
fromMaybe2  nothing  nothing = nothing

instance
  Reflects-These
    : {P : Type ℓ} {Q : Type ℓ′} {x y : Bool}
    → ⦃ rp : Reflects P x ⦄ ⦃ rq : Reflects Q y ⦄ → Reflects (These P Q) (x or y)
  Reflects-These {x = true}  {y = true}  ⦃ ofʸ p ⦄  ⦃ ofʸ q ⦄  = ofʸ (these p q)
  Reflects-These {x = true}  {y = false} ⦃ ofʸ p ⦄  ⦃ ofⁿ ¬q ⦄ = ofʸ (this p)
  Reflects-These {x = false} {y = true}  ⦃ ofⁿ ¬p ⦄ ⦃ ofʸ q ⦄  = ofʸ (that q)
  Reflects-These {x = false} {y = false} ⦃ ofⁿ ¬p ⦄ ⦃ ofⁿ ¬q ⦄ = ofⁿ (rec ¬p ¬q (λ _ → ¬q))

reflects-these : {x y : Bool} → Reflects (These ⌞ x ⌟ ⌞ y ⌟) (x or y)
reflects-these = auto
