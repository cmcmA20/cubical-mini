{-# OPTIONS --safe #-}
module Categories.Diagram.Terminal where

open import Categories.Prelude

module _ {o h} (C : Precategory o h) where

  open import Categories.Morphism C

  is-terminal : Ob → Type _
  is-terminal ob = (x : Ob) → is-contr (x ⇒ ob)

  record Terminal : Type (o ⊔ h) where
    no-eta-equality
    constructor mk-terminal
    field
      top : Ob
      has-⊤ : is-terminal top

    ! : {x : Ob} → x ⇒ top
    ! = centre $ has-⊤ _

    !-unique : {x : Ob} (h : x ⇒ top) → ! ＝ h
    !-unique = paths $ has-⊤ _

    !-unique² : {x : Ob} (f g : x ⇒ top) → f ＝ g
    !-unique² =  is-contr→is-prop (has-⊤ _)

  open Terminal

  unquoteDecl Terminal-Iso = declare-record-iso Terminal-Iso (quote Terminal)

  !-invertible : (t₁ t₂ : Terminal) → is-invertible (! t₁ {top t₂})
  !-invertible t₁ t₂ = make-invertible (! t₂) (!-unique² t₁ _ _) (!-unique² t₂ _ _)

  ⊤-unique : (t₁ t₂ : Terminal) → top t₁ ≅ top t₂
  ⊤-unique t₁ t₂ = invertible→iso (! t₂) (!-invertible t₂ t₁)

  opaque
    ⊤-contractible : is-category C → is-prop Terminal
    ⊤-contractible cat = ≅→is-of-hlevel 1 Terminal-Iso $
      λ u v → cat .to-path (⊤-unique (mk-terminal $ₜ² u) (mk-terminal $ₜ² v))
      ,ₚ prop!

    ≅→is-terminal : ∀ {A B} → A ≅ B → is-terminal A → is-terminal B
    ≅→is-terminal isom term x = isom .to ∘ centre (term x) , λ h →
      isom .to ∘ ⌜ centre (term x) ⌝ ~⟨ ap! (paths (term x) _) ⟩
      isom .to ∘ isom .from ∘ h      ~⟨ assoc _ _ _ ⟩
      ⌜ isom .to ∘ isom .from ⌝ ∘ h  ~⟨ ap! (isom .inv-l) ⟩
      id ∘ h                         ~⟨ id-l _ ⟩
      h                              ∎


instance
  ⊤-Terminal : ∀ {o ℓ} {C : Precategory o ℓ} ⦃ ter : Terminal C ⦄ → ⊤-notation ⌞ C ⌟
  ⊤-Terminal ⦃ ter ⦄ .⊤ = ter .Terminal.top
