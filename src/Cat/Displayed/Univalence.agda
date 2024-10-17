{-# OPTIONS --safe #-}
open import Cat.Displayed.Base
open import Cat.Prelude

module Cat.Displayed.Univalence {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

open import Cat.Displayed.Total

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Morphism

private
  module B = Cat.Morphism B
  module ∫E = Cat.Morphism (∫ E)
open Cat.Displayed.Morphism E
open Displayed E
open Total-hom

is-categoryᵈ : Type _
is-categoryᵈ =
  ∀ {x y} (f : x ≊ y) (A : Ob[ x ]) → is-prop (Σ[ B ꞉ Ob[ y ] ] (A ≊[ f ] B))

open Biinv

module _ (base-c : is-category B) (disp-c : is-categoryᵈ) where
  open _≊[_]_
  private
    piece-together
      : ∀ {x y} (p : x ≊ y) {A : Ob[ x ]} {B : Ob[ y ]} (f : A ≊[ p ] B)
      → (x , A) ≊ (y , B)
    piece-together p f = biinv
      (total-hom (p .to) (f .toᵈ))
      (total-hom (p .from) (f .fromᵈ))
      (total-hom-path (p .from-is-retraction) (f .from-is-retractionᵈ))
      (total-hom (p .section) (f .sectionᵈ))
      (total-hom-path (p .is-section) (f .is-sectionᵈ))

    contract-vertical-equiv
      : ∀ {x : B.Ob} {A : Ob[ x ]} (B : Ob[ x ]) (f : A ≊↓ B)
      → Path (Σ[ z ꞉ ∫E.Ob ] ((x , A) ≊ z))
          ((x , A) , refl)
          ((x , B) , piece-together refl f)
    contract-vertical-equiv {x} {A} B f
      =  (λ i → x , pair i .fst)
      ,ₚ ≊-pathᴾ refl _ (total-hom-pathᴾ refl refl refl (λ i → pair i .fst) refl (λ i → pair i .snd .toᵈ))
      where
        pair = disp-c refl A
          (A , id-equiv↓)
          (B , f)

  is-category-total : is-category (∫ E)
  is-category-total = total-cat where
    wrapper
      : ∀ {x y} (p : x ≊ y) (A : Ob[ x ]) (B : Ob[ y ]) (f : A ≊[ p ] B)
      → Path (Σ[ z ꞉ ∫E.Ob ] ((x , A) ≊ z))
          ((x , A) , refl)
          ((y , B) , piece-together p f)
    wrapper p A =
      Univalent.J-equiv base-c
        (λ y p → (B : Ob[ y ]) (f : A ≊[ p ] B)
               → ((_ , A) , refl) ＝ (((y , B) , piece-together p f)))
        contract-vertical-equiv
        p

    total-cat : is-category (∫ E)
    total-cat .to-path p = ap fst $
      wrapper (total-equiv→equiv E p) _ _ (total-equiv→equiv[] E p)
    total-cat .to-path-over p i .to =
      wrapper (total-equiv→equiv E p) _ _ (total-equiv→equiv[] E p) i .snd .to
    total-cat .to-path-over p i .has-biinv .fst .retraction =
      wrapper (total-equiv→equiv E p) _ _ (total-equiv→equiv[] E p) i .snd .has-biinv .fst .retraction
    total-cat .to-path-over p i .has-biinv .fst .is-retraction =
      wrapper (total-equiv→equiv E p) _ _ (total-equiv→equiv[] E p) i .snd .has-biinv .fst .is-retraction
    total-cat .to-path-over p i .has-biinv .snd .section =
      wrapper (total-equiv→equiv E p) _ _ (total-equiv→equiv[] E p) i .snd .has-biinv .snd .section
    total-cat .to-path-over p i .has-biinv .snd .is-section =
      wrapper (total-equiv→equiv E p) _ _ (total-equiv→equiv[] E p) i .snd .has-biinv .snd .is-section

is-category-fibrewise
  : is-category B
  → (∀ {x} (A : Ob[ x ]) → is-prop (Σ[ B ꞉ Ob[ x ] ] (A ≊↓ B)))
  → is-categoryᵈ
is-category-fibrewise base-c wit f A =
  Univalent.J-equiv base-c (λ y p → is-prop (Σ[ B ꞉ Ob[ y ] ] (A ≊[ p ] B))) (wit A) f
