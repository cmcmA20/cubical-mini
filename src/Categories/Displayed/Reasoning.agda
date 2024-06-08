{-# OPTIONS --safe #-}
open import Categories.Displayed.Base
open import Categories.Prelude

module Categories.Displayed.Reasoning {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

import Categories.Morphism

private
  module E = Displayed E
  module B = Categories.Morphism B

hom[_] : ∀ {a b x y} {f g : B.Hom a b} → f ＝ g → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[_] = subst {B = λ h → E.Hom[ h ] _ _}

hom[_]⁻ : ∀ {a b x y} {f g : B.Hom a b} → g ＝ f → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[ p ]⁻ = hom[ sym p ]

reindex
  : ∀ {a b x y} {f g : B.Hom a b} (p q : f ＝ g) {f′ : E.Hom[ f ] x y}
  → hom[ p ] f′ ＝ hom[ q ] f′
reindex p q {f′} = ap (λ e → hom[ e ] f′) (B.Hom-set _ _ _ _ p q)

cast[]
  : ∀ {a b x y} {f g : B.Hom a b} {f′ : E.Hom[ f ] x y} {g′ : E.Hom[ g ] x y}
  → {p q : f ＝ g}
  → f′ E.＝[ p ] g′
  → f′ E.＝[ q ] g′
cast[] {f} {g} {f′} {g′} {p} {q} r =
  coe0→1 (λ i → f′ E.＝[ B.Hom-set _ _ f g p q i ] g′) r

hom[]-∙
  : ∀ {a b x y} {f g h : B.Hom a b} (p : f ＝ g) (q : g ＝ h)
      {f′ : E.Hom[ f ] x y}
  → hom[ q ] (hom[ p ] f′) ＝ hom[ p ∙ q ] f′
hom[]-∙ p q = sym (subst-comp (λ h → E.Hom[ h ] _ _) _ _ _)

duplicate
  : ∀ {a b x y} {f f′ g : B.Hom a b} (p : f ＝ g) (q : f′ ＝ g) (r : f ＝ f′)
      {f′ : E.Hom[ f ] x y}
  → hom[ p ] f′ ＝ hom[ q ] (hom[ r ] f′)
duplicate p q r = reindex _ _ ∙ sym (hom[]-∙ r q)

hom[] : ∀ {a b x y} {f g : B.Hom a b} {p : f ＝ g} → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[] {p} f′ = hom[ p ] f′

-- TODO a ton of combinators
