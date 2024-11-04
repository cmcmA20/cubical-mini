{-# OPTIONS --safe #-}
open import Cat.Prelude

module Cat.Constructions.Supp {ℓᵃ} (A : Set ℓᵃ) where

open import Cat.Displayed.Univalence.Thin
import Cat.Morphism

open import Meta.Effect

open import Data.Bool as Bool

open Precategory

private variable
  ℓ ℓ′ : Level
  X : 𝒰 ℓ
  Y : 𝒰 ℓ′

record Supported {ℓ} (X : 𝒰 ℓ) : 𝒰 (ℓᵃ ⊔ ℓ) where
  no-eta-equality
  field
    support : X ⇒ ⌞ A ⌟ ⇒ Bool
    support-is-finite : Π[ x ꞉ X ] is-bishop-finite (Σ[ a ꞉ A ] is-true (support x a))

open Supported

unquoteDecl supported-iso = declare-record-iso supported-iso (quote Supported)

record Supported-hom {ℓ ℓ′} {X : 𝒰 ℓ} {Y : 𝒰 ℓ′}
  (S : Supported X) (S′ : Supported Y) (f : X → Y) : 𝒰 (ℓᵃ ⊔ ℓ ⊔ ℓ′)
  where
    no-eta-equality
    field sub-supp : Π[ x ꞉ X ] S′ .support (f x) ⊆ S .support x

open Supported-hom

unquoteDecl H-Level-supported-hom =
  declare-record-hlevel 1 H-Level-supported-hom (quote Supported-hom)

Supported-structure : ∀ ℓ → Thin-structure (Types ℓ) (ℓ ⊔ ℓᵃ) Supported
Supported-structure ℓ .is-hom f X Y = el! (Supported-hom X Y f)
Supported-structure _ .id-is-hom .sub-supp _ = refl
Supported-structure _ .∘-is-hom f g p q .sub-supp x = q .sub-supp x ∘ₜ p .sub-supp _
Supported-structure _ .id-hom-unique {s} {t} p q = pure $ Equiv.injective
  (≅ₜ→≃ supported-iso) $ Σ-prop-path! $ ext $ λ x a →
  boolean-pred-ext (s .support x) (t .support x) (q .sub-supp x) (p .sub-supp x) $ₚ a

Supp : ∀ ℓ → Precategory (ℓᵃ ⊔ ℓsuc ℓ) (ℓᵃ ⊔ ℓ)
Supp ℓ = Structured-objects (Supported-structure ℓ)

module Supp {ℓ} = Cat.Morphism (Supp ℓ)
