{-# OPTIONS --safe #-}
module Data.Fin.Computational.Instances.Ord where

open import Meta.Prelude

open import Meta.Ord

open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Path
open import Data.Nat.Instances.Ord

private variable
  @0 n : ℕ

Ord-Fin : Ord (Fin n)
Ord-Fin .Ord.ℓo = 0ℓ
Ord-Fin .Ord._<_ (mk-fin x) (mk-fin y) = x < y
Ord-Fin .Ord.<-thin {mk-fin x} {mk-fin y} =
  Ord-ℕ .Ord.<-thin {x} {y}
Ord-Fin .Ord.<-trans {mk-fin x} {mk-fin y} {mk-fin z} =
  Ord-ℕ .Ord.<-trans {x} {y} {z}
Ord-Fin .Ord._≤?_ (mk-fin x) (mk-fin y) = Tri-elim
  {C = λ _ → Tri _ _ _}
  (λ x<y x≠y y≮x → lt x<y (λ x=y → x≠y (mk-fin-inj x=y)) y≮x)
  (λ x≮y x=y y≮x → eq x≮y (fin-ext x=y) y≮x)
  (λ x≮y x≠y y<x → gt x≮y (λ x=y → x≠y (mk-fin-inj x=y)) y<x)
  (x ≤? y)
