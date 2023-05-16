{-# OPTIONS --safe #-}
module Data.List.Instances where

open import Foundations.Base
open import Meta.FromProduct
open import Meta.Idiom
open import Meta.Foldable
open import Meta.Traverse

open import Data.List.Base

private variable
  ℓ : Level
  A : Type ℓ

instance
  Map-List : Map (eff List)
  Map-List .Map._<$>_ = map

  From-prod-List : From-product A (λ _ → List A)
  From-prod-List .From-product.from-prod = go where
    go : ∀ n → Vecₓ A n → List A
    go zero xs                = []
    go (suc zero) xs          = xs ∷ []
    go (suc (suc n)) (x , xs) = x ∷ go (suc n) xs

  Traverse-List : Traverse (eff List)
  Traverse-List .Traverse.traverse {M = M} {a = a} {b = b} = go where
    private module M = Effect M
    go : (a → M.₀ b) → List a → M.₀ (List b)
    go f []       = pure []
    go f (x ∷ xs) = ⦇ f x ∷ go f xs ⦈

  Foldable-List : Foldable (eff List)
  Foldable-List .foldr = fold-r
