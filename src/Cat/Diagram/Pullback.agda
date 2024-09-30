{-# OPTIONS --safe #-}
open import Cat.Prelude

module Cat.Diagram.Pullback {ℓ ℓ′} (C : Precategory ℓ ℓ′) where

import Cat.Morphism
open Cat.Morphism C
private variable
  P′ X Y Z : Ob
  h p₁′ p₂′ : Hom X Y

record is-pullback {P : Ob} (p₁ : P ⇒ X) (f : X ⇒ Z) (p₂ : P ⇒ Y) (g : Y ⇒ Z)
  : Type (ℓ ⊔ ℓ′) where

  no-eta-equality
  field
    square   : f ∘ p₁ ＝ g ∘ p₂
    universal : {P′ : Ob} {p₁′ : P′ ⇒ X} {p₂′ : P′ ⇒ Y}
              → f ∘ p₁′ ＝ g ∘ p₂′ → P′ ⇒ P
    p₁∘universal : {p : f ∘ p₁′ ＝ g ∘ p₂′} → p₁ ∘ universal p ＝ p₁′
    p₂∘universal : {p : f ∘ p₁′ ＝ g ∘ p₂′} → p₂ ∘ universal p ＝ p₂′

    unique : {p₂′ : P′ ⇒ Y} {p : f ∘ p₁′ ＝ g ∘ p₂′} {lim′ : P′ ⇒ P}
           → p₁ ∘ lim′ ＝ p₁′
           → p₂ ∘ lim′ ＝ p₂′
           → lim′ ＝ universal p

  unique²
    : {p : f ∘ p₁′ ＝ g ∘ p₂′} {lim′ lim″ : Hom P′ P}
    → p₁ ∘ lim′ ＝ p₁′ → p₂ ∘ lim′ ＝ p₂′
    → p₁ ∘ lim″ ＝ p₁′ → p₂ ∘ lim″ ＝ p₂′
    → lim′ ＝ lim″
  unique² {p = o} p q r s = unique {p = o} p q ∙ sym (unique r s)

  pullback-univ
    : ⦃ hl : ∀ {x y} → H-Level 2 (Hom x y) ⦄ {O : Ob}
    → O ⇒ P
    ≃ Σ[ h ꞉ O ⇒ X ] Σ[ h′ ꞉ O ⇒ Y ] (f ∘ h ＝ g ∘ h′)
  pullback-univ .fst h = p₁ ∘ h , p₂ ∘ h , cat! C ∙ ap (_∘ h) square ∙ cat! C
  pullback-univ .snd = is-inv→is-equiv $ invertible (λ (f , g , α) → universal α)
    (fun-ext λ _ → p₁∘universal ,ₚ p₂∘universal ,ₚ prop!)
    (fun-ext λ _ → unique refl refl ⁻¹)


record Pullback {X Y Z : Ob} (f : X ⇒ Z) (g : Y ⇒ Z) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    {apex} : Ob
    p₁ : apex ⇒ X
    p₂ : apex ⇒ Y
    has-is-pb : is-pullback p₁ f p₂ g

  open is-pullback has-is-pb public

has-pullbacks : Type _
has-pullbacks = {A B X : Ob} (f : A ⇒ X) (g : B ⇒ X) → Pullback f g

module Pullbacks (all-pullbacks : has-pullbacks) where
  module pullback {x y z : Ob} (f : x ⇒ z) (g : y ⇒ z) = Pullback (all-pullbacks f g)

  Pb : {x y z : Ob} → x ⇒ z → y ⇒ z → Ob
  Pb = pullback.apex

is-pullback-stable
  : ∀ {ℓ′} → ({a b : Ob} → a ⇒ b → Type ℓ′) → Type _
is-pullback-stable P =
  ∀ {p A B X : Ob} (f : A ⇒ B) (g : X ⇒ B) {f⁺ : p ⇒ X} {p₂ : p ⇒ A}
  → P f → is-pullback f⁺ g p₂ f
  → P f⁺
