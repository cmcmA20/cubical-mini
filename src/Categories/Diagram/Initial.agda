{-# OPTIONS --safe #-}
module Categories.Diagram.Initial where

open import Categories.Prelude

module _ {o h} (C : Precategory o h) where

  open import Categories.Morphism C

  is-initial : Ob → Type _
  is-initial ob = (x : Ob) → is-contr (ob ⇒ x)

  record Initial : Type (o ⊔ h) where
    no-eta-equality
    constructor mk-initial
    field
      bot  : Ob
      has-⊥ : is-initial bot

    ¡ : ∀ {x} → Hom bot x
    ¡ = centre $ has-⊥ _

    ¡-unique : ∀ {x} (h : Hom bot x) → ¡ ＝ h
    ¡-unique = paths $ has-⊥ _

    ¡-unique² : ∀ {x} (f g : Hom bot x) → f ＝ g
    ¡-unique² = is-contr→is-prop (has-⊥ _)

  open Initial

  unquoteDecl Initial-Iso = declare-record-iso Initial-Iso (quote Initial)

  ⊥-unique : (i i′ : Initial) → bot i ≅ bot i′
  ⊥-unique i i′ = make-iso (¡ i) (¡ i′) (¡-unique² i′ _ _) (¡-unique² i _ _)

  opaque
    ⊥-contractible : is-category C → is-prop Initial
    ⊥-contractible cat = ≅→is-of-hlevel 1 Initial-Iso $
      λ x y → cat .to-path (⊥-unique (mk-initial $ₜ² x) (mk-initial $ₜ² y)) ,ₚ prop!


instance
  ⊥-Initial : ∀ {o ℓ} {C : Precategory o ℓ} ⦃ ini : Initial C ⦄ → ⊥-notation ⌞ C ⌟
  ⊥-Initial ⦃ ini ⦄ .⊥ = ini .Initial.bot
