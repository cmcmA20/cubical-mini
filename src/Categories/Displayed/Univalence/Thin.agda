{-# OPTIONS --safe #-}
module Categories.Displayed.Univalence.Thin where

open import Categories.Displayed.Base public
open import Categories.Displayed.Total public
open import Categories.Displayed.Univalence
open import Categories.Prelude

import Categories.Displayed.Morphism
import Categories.Morphism

open Total-hom public
open Precategory
open Displayed
open Categories.Displayed.Morphism
open _≅[_]_

open import Categories.Constructions.Sets

record
  Thin-structure {ℓ o′} ℓ′ (S : Type ℓ → Type o′)
    : Type (ℓsuc ℓ ⊔ o′ ⊔ ℓsuc ℓ′) where
  no-eta-equality
  field
    is-hom    : ∀ {x y : 𝒰 ℓ} → (x → y) → S x → S y → Prop ℓ′
    id-is-hom : ∀ {x} {s : S x} → ⌞ is-hom refl s s ⌟

    ∘-is-hom  :
      ∀ {x y z} {s t u} (f : y → z) (g : x → y)
      → (α : ⌞ is-hom f t u ⌟) (β : ⌞ is-hom g s t ⌟)
      → ⌞ is-hom (f ∘ₜ g) s u ⌟

    id-hom-unique
      : ∀ {x} {s t : S x}
      → ⌞ is-hom refl s t ⌟ → ⌞ is-hom refl t s ⌟ → Erased (s ＝ t)

open Thin-structure public

module _
  {ℓ o′ ℓ′} {S : Type ℓ → Type o′}
  (spec : Thin-structure ℓ′ S) where

  Thin-structure-over : Displayed (Sets ℓ) o′ ℓ′
  Thin-structure-over .Ob[_] x = S ⌞ x ⌟
  Thin-structure-over .Hom[_] f x y = ⌞ spec .is-hom f x y ⌟
  Thin-structure-over .Hom[_]-set = hlevel!
  Thin-structure-over .idᵈ = spec .id-is-hom
  Thin-structure-over ._∘ᵈ_ = spec .∘-is-hom _ _
  Thin-structure-over .id-rᵈ _ = prop!
  Thin-structure-over .id-lᵈ _ = prop!
  Thin-structure-over .assocᵈ _ _ _ = prop!

  Structured-objects : Precategory _ _
  Structured-objects = ∫ Thin-structure-over

  -- TODO
  -- Structured-objects-is-category : is-category Structured-objects
  -- Structured-objects-is-category =
  --   is-category-total Thin-structure-over Sets-is-category $
  --     is-category-fibrewise _ Sets-is-category λ A x y →
  --     Σ-prop-path
  --       (λ _ _ _ → ≅[]-path _ (spec .is-hom _ _ _ .is-tr _ _))
  --       ( spec .id-hom-unique (x .snd .from′) (x .snd .to′)
  --       ∙ spec .id-hom-unique (y .snd .to′) (y .snd .from′))

  Forget-structure : Functor Structured-objects (Sets ℓ)
  Forget-structure = πᶠ Thin-structure-over

  Structured-hom-path : is-faithful Forget-structure
  Structured-hom-path p = total-hom-path Thin-structure-over p prop!

module _ {ℓ o′ ℓ′} {S : Type ℓ → Type o′} {spec : Thin-structure ℓ′ S} where
  private
    module So = Precategory (Structured-objects spec)
    module Som = Categories.Morphism (Structured-objects spec)

  instance
    Extensional-Hom
      : ∀ {a b ℓʳ} ⦃ sa : Extensional (⌞ a ⌟ → ⌞ b ⌟) ℓʳ ⦄
      → Extensional (So.Hom a b) ℓʳ
    Extensional-Hom ⦃ sa ⦄ = set-injective→extensional! (Structured-hom-path spec) sa


  Homomorphism-monic
    : {x y : So.Ob} (f : So.Hom x y)
    → ({a b : ⌞ x ⌟} (p : f # a ＝ f # b) → a ＝ b)
    → Som.is-monic f
  Homomorphism-monic f wit g h p = ext λ x → wit (ap hom p $ₚ x)


record is-equational {ℓ o′ ℓ′} {S : Type ℓ → Type o′} (spec : Thin-structure ℓ′ S) : Type (ℓsuc ℓ ⊔ o′ ⊔ ℓ′) where
  field
    invert-id-hom : ∀ {x} {s t : S x} → ⌞ spec .is-hom refl s t ⌟ → ⌞ spec .is-hom refl t s ⌟

  private
    module So = Precategory (Structured-objects spec)
    module Som = Categories.Morphism (Structured-objects spec)

  ∫-Path
    : ∀ {a b : So.Ob}
    → (f : So.Hom a b)
    → is-equiv (f $_)
    → Erased (a ＝ b)
  ∫-Path {a} {b} f eqv .erased
    =  n-ua (f .hom , eqv)
    ,ₚ Jₑ (λ B e → ∀ st → ⌞ spec .is-hom (e .fst) (a .snd) st ⌟
                        → ＜ a .snd ／ (λ i → S (ua e i)) ＼ st ＞)
        (λ st pres → to-pathᴾ (ap (λ e → subst S e (a .snd)) ua-idₑ
                  ∙∙ transport-refl _
                  ∙∙ spec .id-hom-unique pres (invert-id-hom pres) .erased))
        (f .hom , eqv) (b .snd) (f .preserves)

open is-equational public

Full-substructure
  : ∀ {ℓ o′} ℓ′ (R S : Type ℓ → Type o′)
  → (∀ X → R X ↪ₜ S X)
  → Thin-structure ℓ′ S
  → Thin-structure ℓ′ R
Full-substructure _ R S embed Sst .is-hom f x y =
  Sst .is-hom f (embed _ .fst x) (embed _ .fst y)
Full-substructure _ R S embed Sst .id-is-hom = Sst .id-is-hom
Full-substructure _ R S embed Sst .∘-is-hom = Sst .∘-is-hom
Full-substructure _ R S embed Sst .id-hom-unique α β .erased =
  is-embedding→injective (embed _ .snd) (Sst .id-hom-unique α β .erased)
