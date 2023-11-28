{-# OPTIONS --safe #-}
module Data.HVec.Base where

open import Foundations.Base

open import Data.Nat.Base

open import Functions.Variadic public

private variable
  ℓ ℓ′ a b : Level
  n : ℕ
  A : Type a
  B : Type b

Product : ∀ n {ls} → Types n ls → Type (ℓsup n ls)
Product 0             _        = ⊤
Product 1             A        = A
Product (suc (suc n)) (A , As) = A × Product (suc n) As

-- rec
uncurryⁿ : ∀ n {ls} {As : Types n ls} → funⁿ As B → Product n As → B
uncurryⁿ 0             f          = λ _ → f
uncurryⁿ 1             f          = f
uncurryⁿ (suc (suc n)) f (a , as) = uncurryⁿ (suc n) (f a) as

infixr -1 _$ⁿ_
_$ⁿ_ : ∀ {n ls} {As : Types n ls} → funⁿ As B → Product n As → B
_$ⁿ_ = uncurryⁿ _

curryⁿ : ∀ n {ls} {As : Types n ls} {ℓ} {B : Type ℓ}
       → (Product n As → B) → funⁿ As B
curryⁿ 0             f = f _
curryⁿ 1             f = f
curryⁿ (suc (suc n)) f = curryⁿ (suc n) ∘′ curry² f
