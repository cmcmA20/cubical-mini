{-# OPTIONS --safe #-}
module Categories.Constructions.Sets {ℓ} where

open import Categories.Prelude
import Categories.Morphism (Sets ℓ) as Sets

open Iso

iso→equiv : {A B : Set ℓ} → A ≅ B → ⌞ A ⌟ ≃ ⌞ B ⌟
iso→equiv x .fst = x .to
iso→equiv x .snd = is-inv→is-equiv (invertible (x .from) (x .inv-o) (x .inv-i))

@0 Sets-is-category : is-category (Sets ℓ)
Sets-is-category .to-path i = n-ua (iso→equiv i)
Sets-is-category .to-path-over p =
  Sets.≅-pathᴾ refl _ $ fun-ext λ _ → =→ua-pathᴾ _ refl
