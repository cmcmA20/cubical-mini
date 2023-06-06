{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Any where

open import Foundations.Base

open import Correspondences.Base
open import Correspondences.Unary.Decidable

import      Data.Dec as Dec
open import Data.Dec
import      Data.List.Base as List
open List
open import Data.Sum.Base

private variable
  a a′ b b′ : Level
  A : Type a
  P : Pred a′ A
  B : Type b
  x : A
  @0 xs ys : List A

data Any {a a′} {A : Type a} (P : Pred a′ A) : @0 List A → Type (a ⊔ a′) where
  here  :     P x  → Any P (x ∷ xs)
  there : Any P xs → Any P (x ∷ xs)

-- Any! : Pred ℓ′ A → @0 List A → Type _
-- Any! P xs = is-contr (Any P xs)

any-weaken-right : Any P xs → Any P (xs ++ ys)
any-weaken-right (here  p)  = here p
any-weaken-right (there ps) = there (any-weaken-right ps)

any-weaken-left : {xs : List A} → Any P ys → Any P (xs ++ ys)
any-weaken-left {xs = []}    ps = ps
any-weaken-left {xs = _ ∷ _} ps = there (any-weaken-left ps)

any? : Decidable P → Decidable (λ xs → Any P xs)
any? P? []       = no (λ ())
any? P? (x ∷ xs) =
  Dec.map [ here , there ]ᵤ
          (λ { ¬ps (here  p)  → ¬ps (inl p)
             ; ¬ps (there ps) → ¬ps (inr ps) })
          (P? x ∨ᵈ any? P? xs)

any-ap
  : (P : Pred a′ A) (Q : Pred b′ B)
    {f : A → B} (f′ : ∀{x} → P x → Q (f x))
    (@0 xs : List A) → Any P xs → Any Q (List.map f xs)
any-ap P Q f′ (x ∷ xs) (here  p)  = here (f′ p)
any-ap P Q f′ (x ∷ xs) (there ps) = there (any-ap P Q f′ xs ps)
