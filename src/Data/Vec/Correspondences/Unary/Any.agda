{-# OPTIONS --safe #-}
module Data.Vec.Correspondences.Unary.Any where

open import Foundations.Base

open import Correspondences.Base
open import Correspondences.Unary.Decidable

import      Data.Dec as Dec
open import Data.Dec
open import Data.Fin.Base
import      Data.Vec.Base as Vec
open Vec
open import Data.Vec.Properties
open import Data.Sum.Base

private variable
  a a′ b b′ : Level
  A : Type a
  P : Pred a′ A
  B : Type b
  x : A
  @0 m n : ℕ
  @0 xs : Vec A m
  @0 ys : Vec A n

data Any {a a′} {A : Type a} (P : Pred a′ A) : @0 Vec A n → Type (a ⊔ a′) where
  here  :     P x  → Any P (x ∷ xs)
  there : Any P xs → Any P (x ∷ xs)

Any′ : ∀ {a a′} {n} {A : Type a} (P : Pred a′ A) → Vec A n → Type _
Any′ {n} P xs = Σ[ idx ꞉ Fin n ] P (lookup xs idx)

any-weaken-right : {m : ℕ} {@0 xs : Vec A m} → Any P xs → Any P (xs ++ ys)
any-weaken-right {m = suc _} (here  p)  = here p
any-weaken-right {m = suc _} (there ps) = there (any-weaken-right ps)

any-weaken-left : {xs : Vec A n} → Any P ys → Any P (xs ++ ys)
any-weaken-left {xs = []}    ps = ps
any-weaken-left {xs = _ ∷ _} ps = there (any-weaken-left ps)

any? : Decidable P → Decidable (λ xs → Any P {n = n} xs)
any? P? []       = no (λ ())
any? P? (x ∷ xs) =
  Dec.map [ here , there ]ᵤ
          (λ { ¬ps (here  p)  → ¬ps (inl p)
             ; ¬ps (there ps) → ¬ps (inr ps) })
          (P? x ∨ᵈ any? P? xs)

any′? : {n : ℕ} → Decidable P → Decidable (λ xs → Any′ {n = n} P xs)
any′? {n = 0}     P? [] = no λ()
any′? {n = suc n} P? (x ∷ xs) =
  Dec.map [ (fzero ,_) , (λ { (i , q) → fsuc i , q }) ]ᵤ
          (λ { ¬ps (fzero  , p ) → ¬ps (inl p)
             ; ¬ps (fsuc i , ps) → ¬ps (inr (_ , ps)) })
          (P? x ∨ᵈ any′? P? xs)

any-ap
  : (P : Pred a′ A) (Q : Pred b′ B)
    {f : A → B} (f′ : ∀{x} → P x → Q (f x))
    {n : ℕ} (@0 xs : Vec A n) → Any P xs → Any Q (Vec.map f xs)
any-ap P Q f′ {n = suc _} (_ ∷ _)  (here  p)  = here (f′ p)
any-ap P Q f′ {n = suc _} (_ ∷ xs) (there ps) = there (any-ap P Q f′ xs ps)
