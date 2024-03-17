{-# OPTIONS --safe #-}
open import Categories.Prelude

module Categories.Constructions.Supp {ℓᵃ} (A : Set ℓᵃ) where

open import Categories.Displayed.Univalence.Thin
import Categories.Morphism

open import Data.Bool  as Bool
open import Data.Empty as ⊥
open import Data.Unit  as ⊤

open Precategory

private variable
  ℓ ℓ′ : Level
  X : 𝒰 ℓ
  Y : 𝒰 ℓ′

instance
  H-Level-sub : ∀ {n} {X : 𝒰 ℓ} {P Q : X → Bool} → H-Level (suc n) (P ⊆ Q)
  H-Level-sub {Q} = hlevel-prop-instance $
    Π-is-of-hlevel-implicit _ λ x →
    Bool.elim {P = λ z → is-prop (_ → ⟦ z ⟧ᵇ)}
    hlevel! hlevel! (Q x)

record Supported {ℓ} (X : 𝒰 ℓ) : 𝒰 (ℓᵃ ⊔ ℓ) where
  no-eta-equality
  field
    support : X → A →̇ Bool
    support-is-finite : Π[ x ꞉ X ] is-bishop-finite (Σ[ a ꞉ A ] ⟦ support x a ⟧ᵇ)

open Supported

unquoteDecl supported-iso = declare-record-iso supported-iso (quote Supported)

record Supported-hom {ℓ ℓ′} {X : 𝒰 ℓ} {Y : 𝒰 ℓ′}
  (S : Supported X) (S′ : Supported Y) (f : X → Y) : 𝒰 (ℓᵃ ⊔ ℓ ⊔ ℓ′)
  where
    no-eta-equality
    field sub-supp : Π[ x ꞉ X ] S′ .support (f x) ⊆ S .support x

open Supported-hom

unquoteDecl supported-hom-iso = declare-record-iso supported-hom-iso (quote Supported-hom)

supported-hom-is-prop : ∀ {S : Supported X} {S′ : Supported Y} {f} → is-prop (Supported-hom S S′ f)
supported-hom-is-prop = iso→is-of-hlevel _ supported-hom-iso hlevel!

instance
  H-Level-supported-hom : ∀ {n} {S : Supported X} {S′ : Supported Y} {f} → H-Level (suc n) (Supported-hom S S′ f)
  H-Level-supported-hom = hlevel-prop-instance supported-hom-is-prop

Supported-structure : ∀ ℓ → Thin-structure {ℓ} (ℓ ⊔ ℓᵃ) Supported
Supported-structure ℓ .is-hom f X Y = el! (Supported-hom X Y f)
Supported-structure _ .id-is-hom .sub-supp _ = refl
Supported-structure _ .∘-is-hom f g p q .sub-supp x = q .sub-supp x ∘ₜ p .sub-supp _
Supported-structure _ .id-hom-unique {s} {t} p q = pure $ Equiv.injective
  (isoₜ→equiv supported-iso) $ Σ-prop-path hlevel! $ ext $ λ x a →
    happly (boolean-pred-ext (s .support x) (t .support x) (q .sub-supp x) (p .sub-supp x)) a

Supp : ∀ ℓ → Precategory (ℓᵃ ⊔ ℓsuc ℓ) (ℓᵃ ⊔ ℓ)
Supp ℓ = Structured-objects (Supported-structure ℓ)

module Supp {ℓ} = Categories.Morphism (Supp ℓ)
