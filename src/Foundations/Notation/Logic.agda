{-# OPTIONS --safe #-}
module Foundations.Notation.Logic where

open import Foundations.Notation.Underlying
open import Foundations.Prim.Type

-- TODO code duplication makes me sick, but using one generic notation
--      typeclass creates unpleasant goals after normalization

-- Quantifiers

record Π-notation {ℓa ℓb ℓ}
  (A : 𝒰 ℓa) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 6 Π
  field Π : (X : A) (F : ⌞ X ⌟ → B) → R
  syntax Π X (λ x → F) = Π[ x ꞉ X ] F
open Π-notation ⦃ ... ⦄ public
{-# DISPLAY Π-notation.Π _ x f = Π x f #-}

record Πᴱ-notation {ℓa ℓb ℓ}
  (A : 𝒰 ℓa) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 6 Πᴱ
  field Πᴱ : (X : A) (F : @0 ⌞ X ⌟ → B) → R
  syntax Πᴱ X (λ x → F) = Πᴱ[ x ꞉ X ] F
open Πᴱ-notation ⦃ ... ⦄ public
{-# DISPLAY Πᴱ-notation.Πᴱ _ x f = Πᴱ x f #-}

record ∀-notation {ℓa ℓb ℓ}
  (A : 𝒰 ℓa) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 6 ∀′
  field ∀′ : (X : A) (F : ⌞ X ⌟ → B) → R
  syntax ∀′ X (λ x → F) = ∀[ x ꞉ X ] F
open ∀-notation ⦃ ... ⦄ public
{-# DISPLAY ∀-notation.∀′ _ x f = ∀′ x f #-}

record ∀ᴱ-notation {ℓa ℓb ℓ}
  (A : 𝒰 ℓa) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 6 ∀ᴱ
  field ∀ᴱ : (X : A) (F : @0 ⌞ X ⌟ → B) → R
  syntax ∀ᴱ X (λ x → F) = ∀ᴱ[ x ꞉ X ] F
open ∀ᴱ-notation ⦃ ... ⦄ public
{-# DISPLAY ∀ᴱ-notation.∀ᴱ _ x f = ∀ᴱ x f #-}

record Σ-notation {ℓa ℓb ℓ}
  (A : 𝒰 ℓa) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 6 Σ
  field Σ : (X : A) (F : ⌞ X ⌟ → B) → R
  syntax Σ X (λ x → F) = Σ[ x ꞉ X ] F
open Σ-notation ⦃ ... ⦄ public
{-# DISPLAY Σ-notation.Σ _ x f = Σ x f #-}

record ∃-notation {ℓa ℓb ℓ}
  (A : 𝒰 ℓa) ⦃ _ : Underlying A ⦄ (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰ω where
  infixr 6 ∃
  field ∃ : (X : A) (F : ⌞ X ⌟ → B) → R
  syntax ∃ X (λ x → F) = ∃[ x ꞉ X ] F
open ∃-notation ⦃ ... ⦄ public
{-# DISPLAY ∃-notation.∃ _ x f = ∃ x f #-}


-- Connectives

record ×-notation {ℓa ℓb ℓ ℓ′}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰 (ℓa ⊔ ℓb ⊔ ℓ ⊔ ℓsuc ℓ′) where
  infixr 8 _×_
  field
    Constraint : A → B → Type ℓ′
    _×_ : (a : A) (b : B) ⦃ _ : Constraint a b ⦄ → R
open ×-notation ⦃ ... ⦄ public using (_×_)
{-# DISPLAY ×-notation._×_ _ a b = a × b #-}

record ⊕-notation {ℓa ℓb ℓ ℓ′}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰 (ℓa ⊔ ℓb ⊔ ℓ ⊔ ℓsuc ℓ′) where
  infixr 7 _⊕_
  field
    Constraint : A → B → Type ℓ′
    _⊕_ : (a : A) (b : B) ⦃ _ : Constraint a b ⦄ → R
open ⊕-notation ⦃ ... ⦄ public using (_⊕_)
{-# DISPLAY ⊕-notation._⊕_ _ a b = a ⊕ b #-}

record ⊎-notation {ℓa ℓb ℓ ℓ′}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰 (ℓa ⊔ ℓb ⊔ ℓ ⊔ ℓsuc ℓ′) where
  infixr 7 _⊎_
  field
    Constraint : A → B → Type ℓ′
    _⊎_ : (a : A) (b : B) ⦃ _ : Constraint a b ⦄ → R
open ⊎-notation ⦃ ... ⦄ public using (_⊎_)
{-# DISPLAY ⊎-notation._⊎_ _ a b = a ⊎ b #-}

record ⊎₁-notation {ℓa ℓb ℓ ℓ′}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰 (ℓa ⊔ ℓb ⊔ ℓ ⊔ ℓsuc ℓ′) where
  infixr 7 _⊎₁_
  field
    Constraint : A → B → Type ℓ′
    _⊎₁_ : (a : A) (b : B) ⦃ _ : Constraint a b ⦄ → R
open ⊎₁-notation ⦃ ... ⦄ public using (_⊎₁_)
{-# DISPLAY ⊎₁-notation._⊎₁_ _ a b = a ⊎₁ b #-}

record ⊻-notation {ℓa ℓb ℓ ℓ′}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰 (ℓa ⊔ ℓb ⊔ ℓ ⊔ ℓsuc ℓ′) where
  infixr 7 _⊻_
  field
    Constraint : A → B → Type ℓ′
    _⊻_ : (a : A) (b : B) ⦃ _ : Constraint a b ⦄ → R
open ⊻-notation ⦃ ... ⦄ public using (_⊻_)
{-# DISPLAY ⊻-notation._⊻_ _ a b = a ⊻ b #-}

record ⇒-notation {ℓa ℓb ℓ ℓ′}
  (A : 𝒰 ℓa) (B : 𝒰 ℓb) (R : 𝒰 ℓ) : 𝒰 (ℓa ⊔ ℓb ⊔ ℓ ⊔ ℓsuc ℓ′) where
  infixr 5 _⇒_
  field
    Constraint : A → B → Type ℓ′
    _⇒_ : (a : A) (b : B) ⦃ _ : Constraint a b ⦄ → R
open ⇒-notation ⦃ ... ⦄ public using (_⇒_)
{-# DISPLAY ⇒-notation._⇒_ _ a b = a ⇒ b #-}

record ¬-notation {ℓa ℓ ℓ′}
  (A : 𝒰 ℓa) (R : 𝒰 ℓ) : 𝒰 (ℓa ⊔ ℓ ⊔ ℓsuc ℓ′) where
  infixr 0 ¬_
  field
    Constraint : A → Type ℓ′
    ¬_ : (a : A) ⦃ _ : Constraint a ⦄ → R
open ¬-notation ⦃ ... ⦄ public
{-# DISPLAY ¬-notation.¬_ _ a = ¬ a #-}


-- Constants

record ⊥-notation {ℓ}
  (R : 𝒰 ℓ) : 𝒰ω where
  field ⊥ : R
open ⊥-notation ⦃ ... ⦄ public
{-# DISPLAY ⊥-notation.⊥ _ = ⊥ #-}

record ⊤-notation {ℓ}
  (R : 𝒰 ℓ) : 𝒰ω where
  field ⊤ : R
open ⊤-notation ⦃ ... ⦄ public
{-# DISPLAY ⊤-notation.⊤ _ = ⊤ #-}
