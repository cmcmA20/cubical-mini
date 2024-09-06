{-# OPTIONS --safe #-}
module Cat.Diagram.Terminal where

open import Cat.Prelude
import Cat.Morphism

module _ {o h} (C : Precategory o h) where
  open Cat.Morphism C

  is-terminal : Ob → Type _
  is-terminal ob = (x : Ob) → is-contr (x ⇒ ob)

  record Terminal : Type (o ⊔ h) where
    no-eta-equality
    constructor mk-terminal
    field
      top   : Ob
      has-⊤ : is-terminal top

    instance
      ⊤-Terminal : ⊤-notation Ob
      ⊤-Terminal .⊤ = top
    {-# INCOHERENT ⊤-Terminal #-}

    ! : {x : Ob} → x ⇒ ⊤
    ! = centre $ has-⊤ _

    !-unique : {x : Ob} (h : x ⇒ ⊤) → ! ＝ h
    !-unique = paths $ has-⊤ _

    !-unique² : {x : Ob} (f g : x ⇒ ⊤) → f ＝ g
    !-unique² =  is-contr→is-prop (has-⊤ _)

{-# DISPLAY Terminal.top = ⊤ #-}
unquoteDecl Terminal-Iso = declare-record-iso Terminal-Iso (quote Terminal)

module _ {o h} {C : Precategory o h} where
  open Cat.Morphism C
  open Terminal
  open Iso

  !-invertible : (t₁ t₂ : Terminal C) → is-invertible (! t₁ {top t₂})
  !-invertible t₁ t₂ = invertible (! t₂) (!-unique² t₁ _ _) (!-unique² t₂ _ _)

  ⊤-unique : (t₁ t₂ : Terminal C) → top t₁ ≅ top t₂
  ⊤-unique t₁ t₂ = is-inv→≅ (! t₂) (!-invertible t₂ t₁)

  opaque
    terminal-is-prop : is-category C → is-prop (Terminal C)
    terminal-is-prop cat = ≅→is-of-hlevel 1 Terminal-Iso $
      λ u v → cat .to-path (⊤-unique (mk-terminal $ₜ² u) (mk-terminal $ₜ² v))
      ,ₚ prop!

    ≅→is-terminal : {a b : Ob} → a ≅ b → is-terminal C a → is-terminal C b
    ≅→is-terminal isom term x = isom .to ∘ centre (term x) , λ h →
      isom .to ∘ ⌜ centre (term x) ⌝ ~⟨ ap! (paths (term x) _) ⟩
      isom .to ∘ isom .from ∘ h      ~⟨ assoc _ _ _ ⟩
      ⌜ isom .to ∘ isom .from ⌝ ∘ h  ~⟨ ap! (isom .inv-o) ⟩
      id ∘ h                         ~⟨ id-l _ ⟩
      h                              ∎

  instance opaque
    H-Level-Terminal
      : ∀ {n} ⦃ _ : 1 ≤ʰ n ⦄ ⦃ _ : is-category C ⦄
      → H-Level n (Terminal C)
    H-Level-Terminal ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (terminal-is-prop auto)
