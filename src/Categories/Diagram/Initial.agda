{-# OPTIONS --safe #-}
module Categories.Diagram.Initial where

open import Categories.Prelude
import Categories.Morphism

module _ {o h} (C : Precategory o h) where
  open Categories.Morphism C

  is-initial : Ob → Type _
  is-initial ob = (x : Ob) → is-contr (ob ⇒ x)

  record Initial : Type (o ⊔ h) where
    no-eta-equality
    constructor mk-initial
    field
      bot   : Ob
      has-⊥ : is-initial bot

    instance
      ⊥-Initial : ⊥-notation Ob
      ⊥-Initial .⊥ = bot
    {-# INCOHERENT ⊥-Initial #-}

    ¡ : {x : Ob} → ⊥ ⇒ x
    ¡ = centre $ has-⊥ _

    ¡-unique : {x : Ob} (h : ⊥ ⇒ x) → ¡ ＝ h
    ¡-unique = paths $ has-⊥ _

    ¡-unique² : {x : Ob} (f g : ⊥ ⇒ x) → f ＝ g
    ¡-unique² = is-contr→is-prop (has-⊥ _)

{-# DISPLAY Initial.bot = ⊥ #-}
unquoteDecl Initial-Iso = declare-record-iso Initial-Iso (quote Initial)

module _ {o h} {C : Precategory o h} where
  open Categories.Morphism C
  open Initial

  ⊥-unique : (i i′ : Initial C) → bot i ≅ bot i′
  ⊥-unique i i′ = iso (¡ i) (¡ i′) (¡-unique² i′ _ _) (¡-unique² i _ _)

  opaque
    initial-is-prop : is-category C → is-prop (Initial C)
    initial-is-prop cat = ≅→is-of-hlevel 1 Initial-Iso $
      λ x y → cat .to-path (⊥-unique (mk-initial $ₜ² x) (mk-initial $ₜ² y)) ,ₚ prop!

  instance opaque
    H-Level-Initial
      : ∀ {n} ⦃ _ : 1 ≤ʰ n ⦄ ⦃ _ : is-category C ⦄
      → H-Level n (Initial C)
    H-Level-Initial ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (initial-is-prop auto)
