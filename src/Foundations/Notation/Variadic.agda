{-# OPTIONS --safe #-}
module Foundations.Notation.Variadic where

open import Foundations.Notation.Decidability
open import Foundations.Notation.Logic
open import Foundations.Prim.Type

private variable ℓ ℓa ℓb ℓr ℓx : Level

record Variadics : Typeω where
  constructor enable-variadic-connectives
  instance
    ×-Variadic
      : {A : Type ℓa} {B : Type ℓb} {R : Type ℓr}
        {X : Type ℓx} ⦃ im : ×-notation {ℓ′ = ℓ} A B R ⦄
      → ×-notation (X → A) (X → B) (X → R)
    ×-Variadic ⦃ im ⦄ .×-notation.Constraint f g =
      ∀ {x} → im .×-notation.Constraint (f x) (g x)
    ×-Variadic .×-notation._×_ f g x = f x × g x
    {-# OVERLAPPING ×-Variadic #-}

    ⊕-Variadic
      : {A : Type ℓa} {B : Type ℓb} {R : Type ℓr}
        {X : Type ℓx} ⦃ im : ⊕-notation {ℓ′ = ℓ} A B R ⦄
      → ⊕-notation (X → A) (X → B) (X → R)
    ⊕-Variadic ⦃ im ⦄ .⊕-notation.Constraint f g =
      ∀ {x} → im .⊕-notation.Constraint (f x) (g x)
    ⊕-Variadic .⊕-notation._⊕_ f g x = f x ⊕ g x
    {-# OVERLAPPING ⊕-Variadic #-}

    ⊎-Variadic
      : {A : Type ℓa} {B : Type ℓb} {R : Type ℓr}
        {X : Type ℓx} ⦃ im : ⊎-notation {ℓ′ = ℓ} A B R ⦄
      → ⊎-notation (X → A) (X → B) (X → R)
    ⊎-Variadic ⦃ im ⦄ .⊎-notation.Constraint f g =
      ∀ {x} → im .⊎-notation.Constraint (f x) (g x)
    ⊎-Variadic .⊎-notation._⊎_ f g x = f x ⊎ g x
    {-# OVERLAPPING ⊎-Variadic #-}

    ⊎₁-Variadic
      : {A : Type ℓa} {B : Type ℓb} {R : Type ℓr}
        {X : Type ℓx} ⦃ im : ⊎₁-notation {ℓ′ = ℓ} A B R ⦄
      → ⊎₁-notation (X → A) (X → B) (X → R)
    ⊎₁-Variadic ⦃ im ⦄ .⊎₁-notation.Constraint f g =
      ∀ {x} → im .⊎₁-notation.Constraint (f x) (g x)
    ⊎₁-Variadic .⊎₁-notation._⊎₁_ f g x = f x ⊎₁ g x
    {-# OVERLAPPING ⊎₁-Variadic #-}

    ⊻-Variadic
      : {A : Type ℓa} {B : Type ℓb} {R : Type ℓr}
        {X : Type ℓx} ⦃ im : ⊻-notation {ℓ′ = ℓ} A B R ⦄
      → ⊻-notation (X → A) (X → B) (X → R)
    ⊻-Variadic ⦃ im ⦄ .⊻-notation.Constraint f g =
      ∀ {x} → im .⊻-notation.Constraint (f x) (g x)
    ⊻-Variadic .⊻-notation._⊻_ f g x = f x ⊻ g x
    {-# OVERLAPPING ⊻-Variadic #-}

    ⇒-Variadic
      : {A : Type ℓa} {B : Type ℓb} {R : Type ℓr}
        {X : Type ℓx} ⦃ im : ⇒-notation {ℓ′ = ℓ} A B R ⦄
      → ⇒-notation (X → A) (X → B) (X → R)
    ⇒-Variadic ⦃ im ⦄ .⇒-notation.Constraint f g =
      ∀ {x} → im .⇒-notation.Constraint (f x) (g x)
    ⇒-Variadic .⇒-notation._⇒_ f g x = f x ⇒ g x
    {-# OVERLAPPING ⇒-Variadic #-}

    ¬-Variadic
      : {A : Type ℓa} {R : Type ℓr}
        {X : Type ℓx} ⦃ im : ¬-notation {ℓ′ = ℓ} A R ⦄
      → ¬-notation (X → A) (X → R)
    ¬-Variadic ⦃ im ⦄ .¬-notation.Constraint f =
      ∀ {x} → im .¬-notation.Constraint (f x)
    ¬-Variadic .¬_ f x = ¬ f x
    {-# OVERLAPPING ¬-Variadic #-}

    Decidability-Variadic
      : {A : Type ℓ} {X : Type ℓx}
        ⦃ de : Decidability A ⦄
      → Decidability (X → A)
    Decidability-Variadic {ℓx} {X} ⦃ de ⦄ .ℓ-decidability =
      ℓx ⊔ de .Decidability.ℓ-decidability
    Decidability-Variadic {X} ⦃ de ⦄ .Decidable f =
      {x : X} → de .Decidable (f x)
    {-# OVERLAPPING Decidability-Variadic #-}

    Reflectance-Variadic
      : {A : Type ℓ} {B : Type ℓb} {X : Type ℓx}
        ⦃ re : Reflectance A B ⦄
      → Reflectance (X → A) (X → B)
    Reflectance-Variadic {ℓx} ⦃ re ⦄ .ℓ-reflectance =
      ℓx ⊔ re .Reflectance.ℓ-reflectance
    Reflectance-Variadic {X} ⦃ re ⦄ .Reflects f b =
      (x : X) → re .Reflects (f x) (b x)
    {-# OVERLAPPING Reflectance-Variadic #-}
