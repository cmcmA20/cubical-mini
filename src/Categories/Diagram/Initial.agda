{-# OPTIONS --safe #-}
open import Categories.Prelude

module Categories.Diagram.Initial {o h} (C : Precategory o h) where

open import Categories.Morphism C

is-initial : Ob → Type _
is-initial ob = ∀ x → is-contr (Hom ob x)

record Initial : Type (o ⊔ h) where
  no-eta-equality
  constructor mk-initial
  field
    bot  : Ob
    has⊥ : is-initial bot

  ¡ : ∀ {x} → Hom bot x
  ¡ = centre $ has⊥ _

  ¡-unique : ∀ {x} (h : Hom bot x) → ¡ ＝ h
  ¡-unique = paths $ has⊥ _

  ¡-unique² : ∀ {x} (f g : Hom bot x) → f ＝ g
  ¡-unique² = is-prop-β $ is-contr→is-prop (has⊥ _)

open Initial


⊥-unique : (i i′ : Initial) → bot i ≅ bot i′
⊥-unique i i′ = make-iso (¡ i) (¡ i′) (¡-unique² i′ _ _) (¡-unique² i _ _)


opaque
  unfolding is-of-hlevel
  ⊥-contractible : is-category C → is-prop Initial
  ⊥-contractible cat x₁ x₂ i .bot =
    Univalent.iso→path cat (⊥-unique x₁ x₂) i
  ⊥-contractible cat x₁ x₂ i .has⊥ ob =
    is-prop→pathP
      (λ j → is-contr-is-prop
        {A = Hom (Univalent.iso→path cat (⊥-unique x₁ x₂) j) _})
      (x₁ .has⊥ ob) (x₂ .has⊥ ob) i
