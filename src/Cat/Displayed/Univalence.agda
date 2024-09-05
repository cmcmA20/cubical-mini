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
  ∀ {x y} (f : x ≅ y) (A : Ob[ x ]) → is-prop (Σ[ B ꞉ Ob[ y ] ] (A ≅[ f ] B))

open Iso

module _ (base-c : is-category B) (disp-c : is-categoryᵈ) where
  private
    piece-together
      : ∀ {x y} (p : x ≅ y) {A : Ob[ x ]} {B : Ob[ y ]} (f : A ≅[ p ] B)
      → (x , A) ≅ (y , B)
    piece-together p f = iso
      (total-hom (p .to) (f .toᵈ))
      (total-hom (p .from) (f .fromᵈ))
      (total-hom-path (p .inv-o) (f .inv-lᵈ))
      (total-hom-path (p .inv-i) (f .inv-rᵈ))

    contract-vertical-iso
      : ∀ {x : B.Ob} {A : Ob[ x ]} (B : Ob[ x ]) (f : A ≅↓ B)
      → Path (Σ[ z ꞉ ∫E.Ob ] ((x , A) ≅ z))
          ((x , A) , refl)
          ((x , B) , piece-together refl f)
    contract-vertical-iso {x} {A} B f
      =  (λ i → x , pair i .fst)
      ,ₚ (∫E.≅-pathᴾ refl _ (total-hom-pathᴾ refl refl refl (λ i → pair i .fst) refl (λ i → pair i .snd .toᵈ)))
      where
        pair = disp-c refl A
          (A , id-iso↓)
          (B , f)

  is-category-total : is-category (∫ E)
  is-category-total = total-cat where
    wrapper
      : ∀ {x y} (p : x ≅ y) (A : Ob[ x ]) (B : Ob[ y ]) (f : A ≅[ p ] B)
      → Path (Σ[ z ꞉ ∫E.Ob ] ((x , A) ≅ z))
          ((x , A) , refl)
          ((y , B) , piece-together p f)
    wrapper p A =
      Univalent.J-iso base-c
        (λ y p → (B : Ob[ y ]) (f : A ≅[ p ] B)
               → ((_ , A) , refl) ＝ (((y , B) , piece-together p f)))
        contract-vertical-iso
        p

    total-cat : is-category (∫ E)
    total-cat .to-path p = ap fst $
      wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p)
    total-cat .to-path-over p i .to =
      wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p) i .snd .to
    total-cat .to-path-over p i .from =
      wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p) i .snd .from
    total-cat .to-path-over p i .inverses .Inverses.inv-o =
      wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p) i .snd .inv-o
    total-cat .to-path-over p i .inverses .Inverses.inv-i =
      wrapper (total-iso→iso E p) _ _ (total-iso→iso[] E p) i .snd .inv-i

is-category-fibrewise
  : is-category B
  → (∀ {x} (A : Ob[ x ]) → is-prop (Σ[ B ꞉ Ob[ x ] ] (A ≅↓ B)))
  → is-categoryᵈ
is-category-fibrewise base-c wit f A =
  Univalent.J-iso base-c (λ y p → is-prop (Σ[ B ꞉ Ob[ y ] ] (A ≅[ p ] B))) (wit A) f
