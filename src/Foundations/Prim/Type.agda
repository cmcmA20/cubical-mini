{-# OPTIONS --safe #-}
module Foundations.Prim.Type where

open import Agda.Primitive public
  using ()
  renaming (Set to 𝒰)
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

level-of-type : {ℓ : Level} → Type ℓ → Level
level-of-type {ℓ} _ = ℓ

level-of-term : {ℓ : Level} {A : Type ℓ} → A → Level
level-of-term {ℓ} _ = ℓ

record Lift {ℓ} ℓ′ (A : Type ℓ) : Type (ℓ ⊔ ℓ′) where
  constructor lift
  field lower : A
open Lift public

instance
  lift-inst : ∀ {ℓ ℓ′} {A : Type ℓ} → ⦃ A ⦄ → Lift ℓ′ A
  lift-inst ⦃ (a) ⦄ = lift a

record Liftω {ℓ} (A : Type ℓ) : Typeω where
  constructor liftω
  field lower : A

instance
  liftω-inst : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → Liftω A
  liftω-inst ⦃ (a) ⦄ = liftω a
