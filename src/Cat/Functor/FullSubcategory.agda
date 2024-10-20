{-# OPTIONS --safe #-}
open import Cat.Prelude

module Cat.Functor.FullSubcategory {o h} {C : Precategory o h} where

open import Cat.Functor.Equivalence
open import Cat.Functor.Properties

import Cat.Morphism C as C
open Precategory

private variable ℓ : Level

Restrict : (P : C.Ob → Type ℓ) → Precategory (o ⊔ ℓ) h
Restrict P .Ob = Σ[ O ꞉ C ] P O
Restrict P .Hom A B = C.Hom (A .fst) (B .fst)
Restrict P .id = C.id
Restrict P ._∘_ = C._∘_
Restrict P .id-l = C.id-l
Restrict P .id-r = C.id-r
Restrict P .assoc = C.assoc

module _ (P : C.Ob → Type ℓ) where
  import Cat.Morphism (Restrict P) as R
  open Biinv

  sub-equiv→super-equiv : ∀ {A B : Σ C.Ob P} → (A ≊ B) → (A .fst ≊ B .fst)
  sub-equiv→super-equiv e = biinv (e .to) (e .from)
    (e .from-is-retraction) (e .section) (e .is-section)

  super-equiv→sub-equiv : ∀ {A B : Σ C.Ob P} → (A .fst ≊ B .fst) → (A ≊ B)
  super-equiv→sub-equiv e = biinv (e .to) (e .from)
    (e .from-is-retraction) (e .section) (e .is-section)

module _ (P : C.Ob → Type ℓ) ⦃ Ppr : ∀ {x} → H-Level 1 (P x) ⦄ where
  import Cat.Morphism (Restrict P) as R

  @0 Restrict-is-category : is-category C → is-category (Restrict P)
  Restrict-is-category cc .to-path e =
    cc .to-path (sub-equiv→super-equiv P e) ,ₚ prop!
  Restrict-is-category cc .to-path-over e = ≊-pathᴾ refl _
    (λ i → cc .to-path-over (sub-equiv→super-equiv P e) i .Biinv.to)

  module _
    {o′ h′} {D : Precategory o′ h′}
    (F : Functor D (Restrict P)) (pi : is-precat-iso F) where
    module D = Precategory D
    open Biinv
    open Functor
    open is-precat-iso pi

    private
      ffe : ∀ {x y} → D.Hom x y ≃ (F # x ⇒ F # y)
      ffe = _ , has-ff

    @0 iso-restrict→is-category : is-category C → is-category D
    iso-restrict→is-category cc = equiv-path→identity-system λ {a b}
      → ≅ₜ→≃ (iso one two (ext (λ e → Equiv.ε ffe # e .to)) (ext λ e → sym $ Equiv.η ffe # e .to))
      ∙ identity-system-gives-path (Restrict-is-category cc)
      ∙ (_ , is-embedding→is-equiv-on-paths (is-equiv→is-embedding has-ob-equiv)) ⁻¹
      where
      one : ∀ {a b : D.Ob} → a ≊ b → F # a ≊ F # b
      one e = biinv (F # e .to) (F # e .from)
        (F .F-∘ _ _ ⁻¹ ∙ ap$ F (e .from-is-retraction) ∙ F .F-id)
        (F # e .section) (F .F-∘ _ _ ⁻¹ ∙ ap$ F (e .is-section) ∙ F .F-id)
      two : ∀ {a b : D.Ob} → F # a ≊ F # b → a ≊ b
      two e = biinv (ffe ⁻¹ $ e .to) (ffe ⁻¹ $ e .from)
        (Equiv.injective ffe $ F .F-∘ _ _
          ∙ ap² C._∘_ (Equiv.ε ffe # e .from) (Equiv.ε ffe # e .to)
          ∙ e .from-is-retraction ∙ F .F-id ⁻¹)
        (ffe ⁻¹ $ e .section)
        (Equiv.injective ffe $ F .F-∘ _ _
          ∙ ap² C._∘_ (Equiv.ε ffe # e .to) (Equiv.ε ffe # e .section)
          ∙ e .is-section ∙ F .F-id ⁻¹)
