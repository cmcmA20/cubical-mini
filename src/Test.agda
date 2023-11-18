{-# OPTIONS --safe -vtactic.variadic:20 #-}
module Test where

open import Prelude
open import Data.Bool
open import Data.List

module Syntax₁ {V : 𝒰} where
  Ctx = List V

  variable v : V

  data Tm : Ctx → 𝒰 where
    var : Tm [ v ]
    app : ∀[ Tm →̇ Tm →̇ Tm ]
    lam : {v : V} → ∀[ (Tm ∘ (v ∷_)) →̇ Tm ]

  i-tak-tozhe-mozhno : Π[ (Tm ×̇ Tm ×̇ Tm) →̇ Tm ]
  i-tak-tozhe-mozhno = {!!}

module Syntax₂ {V : 𝒰} where
  Ctx = List V

  lam-ctx : V → (T : Ctx → ℕ → 𝒰) → Arrows 2 (List V , ℕ) 𝒰
  lam-ctx v T = 0 %= v ∷_ ⊢ (1 %= suc ⊢ T)

  private variable v : V

  data Tm : Ctx → ℕ → 𝒰 where
    one : {v : V} → Tm [ v ] 1
    two : ∀[ Tm →̇ Tm →̇ Tm ]
    three : {v : V} → ∀[ lam-ctx v Tm →̇ Tm ]


  ro : V → funⁿ (Ctx , ℕ) 𝒰
  ro v = let x = three {v} one in {!!}

module Concrete where
  even? : ℕ → Bool
  even? 0 = true
  even? 1 = false
  even? (suc (suc n)) = even? n

  odd? : ℕ → Bool
  odd? = not ∘ even?

  3-divisible : ℕ → Bool
  3-divisible 0 = true
  3-divisible 1 = false
  3-divisible 2 = false
  3-divisible (suc (suc (suc n))) = 3-divisible n

  kek : Π[ (even? ×̇ odd?) →̇ (not ∘ odd?) ]
  kek n (a , b) with even? n
  ... | false = a
  ... | true = _
