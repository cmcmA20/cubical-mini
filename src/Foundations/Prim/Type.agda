{-# OPTIONS --safe #-}
module Foundations.Prim.Type where

open import Agda.Primitive public
  using ()
  renaming ( Set  to 𝒰
           ; Setω to 𝒰ω )
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

open Liftω public

instance
  liftω-inst : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → Liftω A
  liftω-inst ⦃ (a) ⦄ = liftω a


-- types without runtime representation
record Erased {ℓ} (@0 A : Type ℓ) : Type ℓ where
  constructor erase
  field @0 erased : A

open Erased public

instance
  Erased-default : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → Erased A
  Erased-default ⦃ (a) ⦄ .erased = a
  {-# INCOHERENT Erased-default #-}
