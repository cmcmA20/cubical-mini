{-# OPTIONS --safe #-}
module Data.List.Instances.Bind where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Bind
open import Meta.Effect.Idiom

open import Data.List.Base
open import Data.List.Instances.Idiom public
open import Data.List.Properties

private variable
  ℓ : Level
  A B C : Type ℓ

open Idiom ⦃ ... ⦄
open Bind ⦃ ... ⦄
open Lawful-Bind ⦃ ... ⦄

_>>=ₗ_ : List A → (A → List B) → List B
[]       >>=ₗ _ = []
(x ∷ xs) >>=ₗ f = f x ++ (xs >>=ₗ f)

>>=ₗ-++-app
  : (xs ys : List A) (f : A → List B)
  → ((xs ++ ys) >>=ₗ f) ＝ (xs >>=ₗ f) ++ (ys >>=ₗ f)
>>=ₗ-++-app []       ys f = refl
>>=ₗ-++-app (x ∷ xs) ys f
  = ap (f x ++_) (>>=ₗ-++-app xs ys f)
  ∙ ++-assoc (f x) (xs >>=ₗ f) (ys >>=ₗ f) ⁻¹

instance
  Bind-List : Bind (eff List)
  Bind-List ._>>=_ = _>>=ₗ_

  Lawful-Bind-List : Lawful-Bind (eff List)
  Lawful-Bind-List .>>=-id-l = ++-id-r _
  Lawful-Bind-List .>>=-id-r {A} {mx} = go mx where opaque
    go : (xs : List A) → (xs >>= pure) ＝ xs
    go [] = refl
    go (x ∷ xs) = (x ∷_) # go xs
  Lawful-Bind-List .>>=-assoc {A} {B} {C} {mx} {f} {g} = go mx where opaque
    go : (xs : List A) → (xs >>= f >>= g) ＝ (xs >>= λ x → f x >>= g)
    go [] = refl
    go (x ∷ xs) = >>=ₗ-++-app (f x) (xs >>=ₗ f) g ∙ ap (_ ++_) (go xs)
