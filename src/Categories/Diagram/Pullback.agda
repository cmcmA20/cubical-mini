{-# OPTIONS --safe #-}
open import Categories.Prelude

module Categories.Diagram.Pullback {ℓ ℓ′} (C : Precategory ℓ ℓ′) where

import Categories.Morphism
open Categories.Morphism C
private variable
  P′ X Y Z : Ob
  h p₁′ p₂′ : Hom X Y

record is-pullback {P} (p₁ : Hom P X) (f : Hom X Z) (p₂ : Hom P Y) (g : Hom Y Z)
  : Type (ℓ ⊔ ℓ′) where

  no-eta-equality
  field
    square   : f ∘ p₁ ＝ g ∘ p₂
    universal : {p₁′ : Hom P′ X} {p₂′ : Hom P′ Y}
              → f ∘ p₁′ ＝ g ∘ p₂′ → Hom P′ P
    p₁∘universal : {p : f ∘ p₁′ ＝ g ∘ p₂′} → p₁ ∘ universal p ＝ p₁′
    p₂∘universal : {p : f ∘ p₁′ ＝ g ∘ p₂′} → p₂ ∘ universal p ＝ p₂′

    unique : {p : f ∘ p₁′ ＝ g ∘ p₂′} {lim′ : Hom P′ P}
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
    : ∀ {O}
    → Hom O P
    ≃ Σ[ h ꞉ Hom O X ] Σ[ h′ ꞉ Hom O Y ] (f ∘ h ＝ g ∘ h′)
  pullback-univ .fst h = p₁ ∘ h , p₂ ∘ h , cat! C ∙ ap (_∘ h) square ∙ cat! C
  pullback-univ .snd = is-iso→is-equiv λ where
    .is-iso.inv (f , g , α) → universal α
    .is-iso.rinv x → Σ-pathP p₁∘universal $
      Σ-prop-pathP (λ _ _ → path-is-of-hlevel′ 1 hlevel! _ _) p₂∘universal
    .is-iso.linv _ → sym (unique reflₚ reflₚ)


record Pullback {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    {apex} : Ob
    p₁ : Hom apex X
    p₂ : Hom apex Y
    has-is-pb : is-pullback p₁ f p₂ g

  open is-pullback has-is-pb public

has-pullbacks : Type _
has-pullbacks = ∀ {A B X} (f : Hom A X) (g : Hom B X) → Pullback f g

module Pullbacks (all-pullbacks : has-pullbacks) where
  module pullback {x y z} (f : Hom x z) (g : Hom y z) = Pullback (all-pullbacks f g)

  Pb : ∀ {x y z} → Hom x z → Hom y z → Ob
  Pb = pullback.apex

is-pullback-stable
  : ∀ {ℓ′} → (∀ {a b} → Hom a b → Type ℓ′) → Type _
is-pullback-stable P =
  ∀ {p A B X} (f : Hom A B) (g : Hom X B) {f⁺ : Hom p X} {p₂}
  → P f → is-pullback f⁺ g p₂ f → P f⁺
