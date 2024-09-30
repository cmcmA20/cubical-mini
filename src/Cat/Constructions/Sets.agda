{-# OPTIONS --safe #-}
module Cat.Constructions.Sets {ℓ} where

open import Cat.Prelude
open import Cat.Diagram.Initial
open import Cat.Diagram.Terminal
import Cat.Morphism (Sets ℓ) as Sets

open Iso

iso→equiv : {A B : Set ℓ} → A ≅ B → ⌞ A ⌟ ≃ ⌞ B ⌟
iso→equiv x .fst = x .to
iso→equiv x .snd = is-inv→is-equiv (invertible (x .from) (x .inv-o) (x .inv-i))

@0 Sets-is-category : is-category (Sets ℓ)
Sets-is-category .to-path i = n-ua (iso→equiv i)
Sets-is-category .to-path-over p =
  Sets.≅-pathᴾ refl _ $ fun-ext λ _ → =→ua-pathᴾ _ refl

instance
  Sets-has-initial : Initial (Sets ℓ)
  Sets-has-initial .Initial.bot = ⊥
  Sets-has-initial .Initial.has-⊥ _ .fst = λ ()
  Sets-has-initial .Initial.has-⊥ _ .snd _ _ ()

  Sets-has-terminal : Terminal (Sets ℓ)
  Sets-has-terminal .Terminal.top = ⊤
  Sets-has-terminal .Terminal.has-⊤ _ = (λ _ → _) , λ _ → refl
