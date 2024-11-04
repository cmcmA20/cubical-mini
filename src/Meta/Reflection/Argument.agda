{-# OPTIONS --safe #-}
module Meta.Reflection.Argument where

open import Foundations.Base

open import Meta.Effect.Map

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.Instances.Map
open import Data.Reflection.Argument
open import Data.Reflection.Term

open Map ⦃ ... ⦄

record Has-visibility {ℓ} (A : Type ℓ) : Type ℓ where
  field set-visibility : Visibility → A → A

open Has-visibility ⦃ ... ⦄ public

private variable
  ℓ : Level
  A : Type ℓ

instance
  Has-visibility-arg-info : Has-visibility Arg-info
  Has-visibility-arg-info .set-visibility v (arg-info _ m) = arg-info v m

  Has-visibility-Arg : Has-visibility (Arg A)
  Has-visibility-Arg .set-visibility v (arg ai x) = arg (set-visibility v ai) x

  Has-visibility-Args : Has-visibility (List (Arg A))
  Has-visibility-Args .set-visibility v = map (set-visibility v)

  Has-visibility-Telescope : Has-visibility Telescope
  Has-visibility-Telescope .set-visibility v = map (second (set-visibility v))

hide : ⦃ Has-visibility A ⦄ → A → A
hide = set-visibility hidden

hide-if : ⦃ Has-visibility A ⦄ → Bool → A → A
hide-if true  = hide
hide-if false = id


record Has-quantity {ℓ} (A : Type ℓ) : Type ℓ where
  field set-quantity : Quantity → A → A

open Has-quantity ⦃ ... ⦄ public

instance
  Has-quantity-arg-info : Has-quantity Arg-info
  Has-quantity-arg-info .set-quantity q (arg-info v (modality r _)) = arg-info v (modality r q)

  Has-quantity-Arg : Has-quantity (Arg A)
  Has-quantity-Arg .set-quantity v (arg ai x) = arg (set-quantity v ai) x

  Has-quantity-Args : Has-quantity (List (Arg A))
  Has-quantity-Args .set-quantity q = map (set-quantity q)

  Has-quantity-Telescope : Has-quantity Telescope
  Has-quantity-Telescope .set-quantity q = map (second (set-quantity q))
