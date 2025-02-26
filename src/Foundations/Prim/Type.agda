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
        ; lzero
        ; lsuc)
  renaming ( Prop  to DIProp
           ; Set   to Type
           ; Setω  to Typeω
           ; _⊔_   to _l⊔_ )

level-of-type : {ℓ : Level} → Type ℓ → Level
level-of-type {ℓ} _ = ℓ

level-of-term : {ℓ : Level} {A : Type ℓ} → A → Level
level-of-term {ℓ} _ = ℓ

Fun : {ℓa ℓb : Level} → Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb)
Fun A B = A → B

Corr² : {ℓa ℓb : Level} (ℓ : Level) → Type ℓa → Type ℓb → Type (ℓa l⊔ ℓb l⊔ lsuc ℓ)
Corr² ℓ A B = A → B → Type ℓ


auto : {ℓ : Level} {A : Type ℓ} → ⦃ A ⦄ → A
auto ⦃ (a) ⦄ = a

autoω : {A : Typeω} → ⦃ A ⦄ → A
autoω ⦃ (a) ⦄ = a

-- Explicit type hint
the : {ℓ : Level} (A : Type ℓ) → A → A
the _ a = a
