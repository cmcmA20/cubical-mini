{-# OPTIONS --safe #-}
module Foundations.Prim.Type where

open import Agda.Primitive public
  using ( SSet
        ; SSetω
        ; LevelUniv
        ; Level
        ; _⊔_ )
  renaming ( Prop  to DIProp
           ; Set   to Type
           ; Setω  to Typeω
           ; lzero to 0ℓ
           ; lsuc  to ℓsuc )
open import Agda.Primitive public
  using ()
  renaming (Set to 𝒰)

level-of-type : {ℓ : Level} → Type ℓ → Level
level-of-type {ℓ} _ = ℓ

level-of-term : {ℓ : Level} {A : Type ℓ} → A → Level
level-of-term {ℓ} _ = ℓ

it : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → A
it ⦃ (a) ⦄ = a

record Lift {ℓ} ℓ′ (A : Type ℓ) : Type (ℓ ⊔ ℓ′) where
  constructor lift
  field lower : A
open Lift public

instance
  Lift-inst : ∀ {ℓ ℓ′} {A : Type ℓ} → ⦃ A ⦄ → Lift ℓ′ A
  Lift-inst ⦃ (a) ⦄ = lift a

record Liftω {ℓ} (A : Type ℓ) : Typeω where
  constructor liftω
  field lower : A

instance
  Liftω-inst : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → Liftω A
  Liftω-inst ⦃ (a) ⦄ = liftω a
