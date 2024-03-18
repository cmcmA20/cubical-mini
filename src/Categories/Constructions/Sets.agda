{-# OPTIONS --safe #-}
module Categories.Constructions.Sets {ℓ} where

open import Categories.Prelude
import Categories.Morphism (Sets ℓ) as Sets

iso→equiv : {A B : Set ℓ} → A Sets.≅ B → ⌞ A ⌟ ≃ ⌞ B ⌟
iso→equiv x .fst = x .Sets.to
iso→equiv x .snd = is-iso→is-equiv $ iso x.from (x.inv-l $ₚ_) (x.inv-r $ₚ_)
  where module x = Sets._≅_ x

@0 Sets-is-category : is-category (Sets ℓ)
Sets-is-category .to-path i = n-ua (iso→equiv i)
Sets-is-category .to-path-over p =
  Sets.≅-pathP refl _ $ fun-ext λ _ → path→ua-pathP _ refl
