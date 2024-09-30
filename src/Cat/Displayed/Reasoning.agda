{-# OPTIONS --safe #-}
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Prelude

module Cat.Displayed.Reasoning {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where

import Cat.Morphism

private
  module E = Displayed E
  module B = Cat.Morphism B

private variable
  a b : B.Ob
  x y : E.Ob[ a ]
  f g h : B.Hom a b
  n : HLevel

hom[_] : f ＝ g → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[_] = subst (λ h → E.Hom[ h ] _ _)

hom[_]⁻ : g ＝ f → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[ p ]⁻ = hom[ sym p ]

hom[] : {p : f ＝ g} → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[] {p} f′ = hom[ p ] f′

hom[]-∙
  : {f g h : B.Hom a b} (p : f ＝ g) (q : g ＝ h) {f′ : E.Hom[ f ] x y}
  → hom[ q ] (hom[ p ] f′) ＝ hom[ p ∙ q ] f′
hom[]-∙ p q = sym (subst-comp (λ h → E.Hom[ h ] _ _) _ _ _)

=↑ : {f g : a ⇒ b}
     {x′ : E.Ob[ a ]} {y′ : E.Ob[ b ]}
     {f′ : E.Hom[ f ] x′ y′}
     {g′ : E.Hom[ g ] x′ y′}
     {p : f ＝ g}
   → (f′ E.＝[ p ] g′)
   → (f , f′) ＝ (g , g′)
=↑ = Σ-pathᴾ _

=↓ : {f g : a ⇒ b}
     {x′ : E.Ob[ a ]} {y′ : E.Ob[ b ]}
     {f′ : E.Hom[ f ] x′ y′}
     {g′ : E.Hom[ g ] x′ y′}
   → (Σp : (f , f′) ＝ (g , g′))
   → f′ E.＝[ ap fst Σp ] g′
=↓ = ap snd

module _ ⦃ _ : H-Level 2 (B.Hom a b) ⦄ where

  reindex
    : {f g : B.Hom a b} (p q : f ＝ g) {f′ : E.Hom[ f ] x y}
    → hom[ p ] f′ ＝ hom[ q ] f′
  reindex p q {f′} = ap (λ e → hom[ e ] f′) prop!

  cast[]
    : {f g : B.Hom a b} {f′ : E.Hom[ f ] x y} {g′ : E.Hom[ g ] x y}
    → {p q : f ＝ g}
    → f′ E.＝[ p ] g′
    → f′ E.＝[ q ] g′
  cast[] {f} {g} {f′} {g′} {p} {q} r =
    coe0→1 (λ i → f′ E.＝[ hlevel 2 _ _ p q i ] g′) r

  duplicate
    : {f f′ g : B.Hom a b} (p : f ＝ g) (q : f′ ＝ g) (r : f ＝ f′){f′ : E.Hom[ f ] x y}
    → hom[ p ] f′ ＝ hom[ q ] (hom[ r ] f′)
  duplicate p q r = reindex _ _ ∙ sym (hom[]-∙ r q)

-- -- TODO a ton of combinators
