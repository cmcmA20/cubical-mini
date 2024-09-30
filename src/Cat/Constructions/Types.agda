{-# OPTIONS --safe #-}
module Cat.Constructions.Types {ℓ} where

open import Cat.Prelude
open import Cat.Diagram.Initial
open import Cat.Diagram.Terminal
open import Cat.Morphism (Types ℓ) as Types

open Iso

-- TODO check no-eta
-- @0 Types-is-category : is-category (Types ℓ)
-- Types-is-category .to-path i = ua (≅ₜ→≃ {!!}) -- (iso→equiv i)
-- Types-is-category .to-path-over p = {!!}

instance
  Types-has-initial : Initial (Types ℓ)
  Types-has-initial .Initial.bot = ⊥
  Types-has-initial .Initial.has-⊥ _ .fst = λ ()
  Types-has-initial .Initial.has-⊥ _ .snd _ _ ()

  Types-has-terminal : Terminal (Types ℓ)
  Types-has-terminal .Terminal.top = ⊤
  Types-has-terminal .Terminal.has-⊤ _ = (λ _ → _) , λ _ → refl
