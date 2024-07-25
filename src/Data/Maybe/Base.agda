{-# OPTIONS --safe #-}
module Data.Maybe.Base where

open import Foundations.Base

open import Data.Empty.Base using ()
open import Data.Unit.Base  using ()

open import Agda.Builtin.Maybe public

private variable
  ℓ ℓ′ : Level
  A B C : Type ℓ

rec : B → (A → B) → Maybe A → B
rec b f (just x) = f x
rec b _ nothing  = b

elim : {A : Type ℓ} (B : Maybe A → Type ℓ′)
       (b : B nothing)
       (f : Π[ a ꞉ A ] B (just a))
     → (mx : Maybe A) → B mx
elim B b f nothing  = b
elim B n f (just x) = f x

from-just : A → Maybe A → A
from-just def (just x) = x
from-just def nothing  = def

is-nothing : Maybe A → Type
is-nothing (just _) = ⊥
is-nothing nothing  = ⊤

is-just : Maybe A → Type
is-just (just _) = ⊤
is-just nothing  = ⊥
