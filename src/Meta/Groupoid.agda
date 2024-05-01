{-# OPTIONS --safe #-}
module Meta.Groupoid where

open import Foundations.Prelude
  renaming ( _∙_  to _∙ₚ_
           ; _∘ˢ_ to _∘ₜˢ_
           ; _∘_  to _∘ₜ_
           ; refl to reflₚ
           ; sym  to symₚ
           )

record Reflexive {ℓᵃ} {A : 𝒰 ℓᵃ} {ℓ : Level}
  (_~_ : A → A → 𝒰 ℓ) : 𝒰 (ℓᵃ ⊔ ℓ) where
  no-eta-equality
  field refl : {x : A} → x ~ x

open Reflexive ⦃ ... ⦄ public

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ
  ℓ : Level

instance
  Reflexive-Path : Reflexive (Path A)
  Reflexive-Path .refl = reflₚ

  Reflexive-Fun : Reflexive (Fun {ℓ})
  Reflexive-Fun .refl = id

  Reflexive-≃ : Reflexive (_≃_ {ℓ})
  Reflexive-≃ .refl = idₑ

  Reflexive-≃ᴱ : Reflexive (_≃ᴱ_ {ℓ})
  Reflexive-≃ᴱ .refl = ≃→≃ᴱ idₑ

  Reflexive-Iso : Reflexive (Iso {ℓ})
  Reflexive-Iso .refl = idᵢ

-- "untyped" raw reflexivity is just being pointed
record Reflexiveᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field mempty : A

open Reflexiveᵘ ⦃ ... ⦄ public

instance
  Reflexiveᵘ→Reflexive : ⦃ Reflexiveᵘ A ⦄ → Reflexive {A = A} λ _ _ → A
  Reflexiveᵘ→Reflexive .refl = mempty
  {-# INCOHERENT Reflexiveᵘ→Reflexive #-}


record Symmetric {ℓᵃ ℓᵇ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {ℓ ℓ′ : Level}
  (I : A → B → 𝒰 ℓ) (O : B → A → 𝒰 ℓ′) : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓ ⊔ ℓ′) where
  no-eta-equality
  infix 90 _⁻¹
  field _⁻¹ : {x : A} {y : B} → I x y → O y x

  sym = _⁻¹

open Symmetric ⦃ ... ⦄ public

instance
  Symmetric-Path : Symmetric (Path A) (Path A)
  Symmetric-Path ._⁻¹ = symₚ

  Symmetric-≃ : Symmetric (_≃_ {ℓᵃ} {ℓᵇ}) _≃_
  Symmetric-≃ ._⁻¹ = _ₑ⁻¹

  Symmetric-≃ᴱ : Symmetric (_≃ᴱ_ {ℓᵃ} {ℓᵇ}) _≃ᴱ_
  Symmetric-≃ᴱ ._⁻¹ = _ᴱₑ⁻¹

  Symmetric-Iso : Symmetric (Iso {ℓᵃ} {ℓᵇ}) Iso
  Symmetric-Iso ._⁻¹ = _ᵢ⁻¹

-- "untyped" raw symmetry is just having an automorphism
record Symmetricˢ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  field inv : A → A

open Symmetricˢ ⦃ ... ⦄ public

instance
  Symmetricˢ→Symmetric
    : ⦃ Symmetricˢ A ⦄
    → Symmetric {A = ⊤} {B = ⊤} (λ _ _ → A) (λ _ _ → A)
  Symmetricˢ→Symmetric ._⁻¹ = inv
  {-# INCOHERENT Symmetricˢ→Symmetric #-}


record Transitive {ℓᵃ ℓᵇ ℓᶜ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ} {ℓl ℓr ℓo : Level}
  (L : A → B → 𝒰 ℓl) (R : B → C → 𝒰 ℓr) (O : A → C → 𝒰 ℓo) : 𝒰 (ℓᵃ ⊔ ℓᵇ ⊔ ℓᶜ ⊔ ℓl ⊔ ℓr ⊔ ℓo) where
  no-eta-equality
  infixr 30 _∙_
  field _∙_ : {x : A} {y : B} {z : C} → L x y → R y z → O x z

  infixr 9 _∘ˢ_
  _∘ˢ_ : {x : A} {y : B} {z : C} → R y z → L x y → O x z
  _∘ˢ_ = flip _∙_

open Transitive ⦃ ... ⦄ public

instance
  Transitive-Path : Transitive (Path A) (Path A) (Path A)
  Transitive-Path ._∙_ = _∙ₚ_

  Transitive-Fun : Transitive (Fun {ℓᵃ} {ℓᵇ}) (Fun {ℓᵇ = ℓᶜ}) Fun
  Transitive-Fun ._∙_ f g = g ∘ₜˢ f

  Transitive-≃ : Transitive (_≃_ {ℓᵃ} {ℓᵇ}) (_≃_ {ℓ' = ℓᶜ}) _≃_
  Transitive-≃ ._∙_  = _∙ₑ_

  Transitive-≃ᴱ : Transitive (_≃ᴱ_ {ℓᵃ} {ℓᵇ}) (_≃ᴱ_ {ℓ′ = ℓᶜ}) _≃ᴱ_
  Transitive-≃ᴱ ._∙_  = _∙ᴱₑ_

  Transitive-Iso : Transitive (Iso {ℓᵃ} {ℓᵇ}) (Iso {ℓ′ = ℓᶜ}) Iso
  Transitive-Iso ._∙_  = _∙ᵢ_

-- "untyped" raw transitivity is just having a binary operation
record Transitiveᵘ {ℓᵃ} (A : 𝒰 ℓᵃ) : 𝒰 ℓᵃ where
  no-eta-equality
  infixr 6 _<>_
  field _<>_ : A → A → A

open Transitiveᵘ ⦃ ... ⦄ public

instance
  Transitiveᵘ→Transitive
    : ⦃ Transitiveᵘ A ⦄
    → Transitive {A = ⊤} {B = ⊤} {C = ⊤} (λ _ _ → A) (λ _ _ → A) (λ _ _ → A)
  Transitiveᵘ→Transitive ._∙_ = _<>_
  {-# INCOHERENT Transitiveᵘ→Transitive #-}
