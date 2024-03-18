{-# OPTIONS --safe #-}
open import Categories.Displayed.Base
open import Categories.Prelude

module Categories.Displayed.Univalence {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

open import Categories.Displayed.Total

import Categories.Displayed.Reasoning
import Categories.Displayed.Morphism
import Categories.Morphism

private
  module B = Categories.Morphism B
  module ∫E = Categories.Morphism (∫ E)
open Categories.Displayed.Morphism E
open Displayed E
open Total-hom

is-categoryᵈ : Type _
is-categoryᵈ =
  ∀ {x y} (f : x B.≅ y) (A : Ob[ x ]) → is-prop (Σ[ B ꞉ Ob[ y ] ] (A ≅[ f ] B))

module _ (base-c : is-category B) (disp-c : is-categoryᵈ) where
  private
    piece-together
      : ∀ {x y} (p : x B.≅ y) {A : Ob[ x ]} {B : Ob[ y ]} (f : A ≅[ p ] B)
      → (x , A) ∫E.≅ (y , B)
    piece-together p f =
      ∫E.make-iso (total-hom (p .B.to) (f .toᵈ)) (total-hom (p .B.from) (f .fromᵈ))
        (total-hom-path E (p .B.inv-l) (f .inv-lᵈ))
        (total-hom-path E (p .B.inv-r) (f .inv-rᵈ))

    contract-vertical-iso
      : ∀ {x} {A : Ob[ x ]} (B : Ob[ x ]) (f : A ≅↓ B)
      → Path (Σ _ ((x , A) ∫E.≅_)) ((x , A) , ∫E.id-iso)
          ((x , B) , piece-together B.id-iso f)
    contract-vertical-iso {x} {A} B f
      =  (λ i → x , pair i .fst)
      ,ₚ (∫E.≅-pathP refl _ (total-hom-pathp E _ _ refl λ i → pair i .snd .toᵈ))
      where
        pair = is-prop-β (disp-c B.id-iso A)
          (A , id-iso↓)
          (B , f)

  is-category-total : is-category (∫ E)
  is-category-total = total-cat where
    wrapper
      : ∀ {x y} (p : x B.≅ y) (A : Ob[ x ]) (B : Ob[ y ]) (f : A ≅[ p ] B)
      → Path (Σ _ ((x , A) ∫E.≅_))
        ((x , A) , ∫E.id-iso)
        ((y , B) , piece-together p f)
    wrapper p A =
      Univalent.J-iso base-c
        (λ y p → (B : Ob[ y ]) (f : A ≅[ p ] B)
               → ((_ , A) , ∫E.id-iso) ＝ (((y , B) , piece-together p f)))
        contract-vertical-iso
        p

    total-cat : is-category (∫ E)
    total-cat .to-path p = ap fst $
        wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p)
    total-cat .to-path-over p = ap snd $
        wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p)

is-category-fibrewise
  : is-category B
  → (∀ {x} (A : Ob[ x ]) → is-prop (Σ[ B ꞉ Ob[ x ] ] (A ≅↓ B)))
  → is-categoryᵈ
is-category-fibrewise base-c wit f A =
  Univalent.J-iso base-c (λ y p → is-prop (Σ[ B ꞉ Ob[ y ] ] (A ≅[ p ] B))) (wit A) f
