{-# OPTIONS --safe #-}
module Cat.Displayed.Univalence.Thin where

open import Cat.Functor.Properties
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Univalence
open import Cat.Prelude

import Cat.Displayed.Morphism
import Cat.Morphism

open Total-hom public
open Displayed
open Cat.Displayed.Morphism

record Thin-structure {o h} (C : Precategory o h)
  {o′} ℓ′ (S : ⌞ C ⌟ → Type o′) : Type (o ⊔ h ⊔ o′ ⊔ ℓsuc ℓ′) where
  no-eta-equality
  private module C = Precategory C
  field
    is-hom    : ∀ {x y : C.Ob} → C.Hom x y → S x → S y → Prop ℓ′
    id-is-hom : ∀ {x} {s : S x} → ⌞ is-hom refl s s ⌟

    ∘-is-hom  :
      ∀ {x y z} {s t u} (f : C.Hom y z) (g : C.Hom x y)
      → (α : ⌞ is-hom f t u ⌟) (β : ⌞ is-hom g s t ⌟)
      → ⌞ is-hom (g ∙ f) s u ⌟

    id-hom-unique
      : ∀ {x} {s t : S x}
      → ⌞ is-hom refl s t ⌟ → ⌞ is-hom refl t s ⌟ → Erased (s ＝ t)

open Thin-structure public

module _
  {o h o′ ℓ′} {C : Precategory o h} {S : ⌞ C ⌟ → Type o′}
  (spec : Thin-structure C ℓ′ S) where

  Thin-structure-over : Displayed C o′ ℓ′
  Thin-structure-over .Ob[_] = S
  Thin-structure-over .Hom[_] f x y = ⌞ spec .is-hom f x y ⌟
  Thin-structure-over .idᵈ = spec .id-is-hom
  Thin-structure-over ._∘ᵈ_ = spec .∘-is-hom _ _
  Thin-structure-over .id-rᵈ _ = prop!
  Thin-structure-over .id-lᵈ _ = prop!
  Thin-structure-over .assocᵈ _ _ _ = prop!

  Structured-objects : Precategory _ _
  Structured-objects = ∫ Thin-structure-over

  @0 Structured-objects-is-category : is-category C → is-category Structured-objects
  Structured-objects-is-category cc =
    is-category-total Thin-structure-over cc $
      is-category-fibrewise _ cc λ A x y →
        Σ-prop-path
          (λ _ _ _ → ext (spec .is-hom _ _ _ .n-Type.carrier-is-tr _ _))
          ( spec .id-hom-unique (x .snd .fromᵈ) (x .snd .toᵈ) .erased
          ∙ spec .id-hom-unique (y .snd .toᵈ) (y .snd .fromᵈ) .erased)

  Forget-structure : Functor Structured-objects C
  Forget-structure = πᶠ Thin-structure-over

  Structured-hom-path : is-faithful Forget-structure
  Structured-hom-path p = total-hom-path p prop!

  open Precategory C
  open Biinv

  record is-equational : Type (o ⊔ o′ ⊔ ℓ′) where
    field invert-id-hom : ∀ {x} {s t : S x} → ⌞ spec .is-hom refl s t ⌟ → ⌞ spec .is-hom refl t s ⌟

    private
      module So = Precategory Structured-objects
      module Som = Cat.Morphism Structured-objects

    ∫-Path
      : ∀ {a b : So.Ob}
        (u : is-category C)
      → (f : So.Hom a b)
      → (eqv : is-biinv (f .hom))
      → Erased (a ＝ b)
    ∫-Path {a = x , sx} {b = y , sy} u f eqv .erased
      =  Univalent.equiv→path u (make-biinv (f .hom) eqv)
      ,ₚ Univalent.J-equiv u (λ B e → ∀ st → ⌞ spec .is-hom (e .to) sx st ⌟
                                    → ＜ sx ／ (λ i → S (Univalent.equiv→path u e i)) ＼ st ＞)
          (λ st pres → to-pathᴾ (ap (λ e → subst S e sx) (Univalent.equiv→path-id u)
                    ∙∙ transport-refl _
                    ∙∙ spec .id-hom-unique pres (invert-id-hom pres) .erased))
           (make-biinv (f .hom) eqv) sy (f .preserves) -- (f .preserves)

  open is-equational ⦃ ... ⦄ public

Full-substructure
  : ∀ {o h o′} {C : Precategory o h}
    ℓ′ (R S : ⌞ C ⌟ → Type o′)
  → (∀ X → R X ↪ₜ S X)
  → Thin-structure C ℓ′ S
  → Thin-structure C ℓ′ R
Full-substructure _ R S embed Sst .is-hom f x y =
  Sst .is-hom f (embed _ .fst x) (embed _ .fst y)
Full-substructure _ R S embed Sst .id-is-hom = Sst .id-is-hom
Full-substructure _ R S embed Sst .∘-is-hom = Sst .∘-is-hom
Full-substructure _ R S embed Sst .id-hom-unique α β .erased =
  is-embedding→injective (embed _ .snd) (Sst .id-hom-unique α β .erased)
