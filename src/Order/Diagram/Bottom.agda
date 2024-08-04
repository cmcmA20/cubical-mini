{-# OPTIONS --safe #-}
module Order.Diagram.Bottom where

open import Categories.Prelude
open import Categories.Diagram.Initial

open import Order.Base
open import Order.Category
open import Order.Diagram.Lub
import Order.Reasoning

module _ {o ℓ} (P : Poset o ℓ) where
  open Order.Reasoning P

  is-bottom : Ob → Type _
  is-bottom bot = (x : Ob) → bot ≤ x

  record Bottom : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      bot   : Ob
      has-⊥ : is-bottom bot

    instance
      ⊥-Bottom : ⊥-notation Ob
      ⊥-Bottom .⊥ = bot

    ¡ : ∀{x} → ⊥ ≤ x
    ¡ = has-⊥ _

{-# DISPLAY Bottom.bot = ⊥ #-}
unquoteDecl Bottom-Iso = declare-record-iso Bottom-Iso (quote Bottom)

module _ {o ℓ} {P : Poset o ℓ} where
  open Order.Reasoning P

  is-bottom→is-lub : ∀ {lub} {f : ⊥ → _} → is-bottom P lub → is-lub P f lub
  is-bottom→is-lub is-bot .is-lub.least x _ = is-bot x

  is-lub→is-bottom : ∀ {lub} {f : ⊥ → _} → is-lub P f lub → is-bottom P lub
  is-lub→is-bottom lub x = lub .is-lub.least x λ ()

  is-bottom≃is-lub : ∀{lub} {f} → is-bottom P lub ≃ is-lub P f lub
  is-bottom≃is-lub = is-bottom→is-lub , biimp-is-equiv! _ is-lub→is-bottom

  bottom-unique : ∀ {x y} → is-bottom P x → is-bottom P y → x ＝ y
  bottom-unique p q = ≤-antisym (p _) (q _)

  Bottom-is-prop : is-prop (Bottom P)
  Bottom-is-prop = ≅→is-of-hlevel 1 Bottom-Iso λ x y → bottom-unique (x .snd) (y .snd) ,ₚ prop!

  instance
    H-Level-Bottom
      : ∀ {n} ⦃ _ : 1 ≤ʰ n ⦄
      → H-Level n (Bottom P)
    H-Level-Bottom ⦃ s≤ʰs _ ⦄ = hlevel-basic-instance 1 Bottom-is-prop

  Bottom→Lub : ∀ {f : ⊥ → _} → Bottom P → Lub P f
  Bottom→Lub bottom .Lub.lub = Bottom.bot bottom
  Bottom→Lub bottom .Lub.has-lub = is-bottom→is-lub (Bottom.has-⊥ bottom)

  Lub→Bottom : ∀ {f : ⊥ → _} → Lub P f → Bottom P
  Lub→Bottom lub .Bottom.bot = Lub.lub lub
  Lub→Bottom lub .Bottom.has-⊥ = is-lub→is-bottom (Lub.has-lub lub)

  Bottom≃Lub : ∀{f} → Bottom P ≃ Lub P f
  Bottom≃Lub = Bottom→Lub , biimp-is-equiv! _ Lub→Bottom

  is-bottom→is-initial : ∀ {x} → is-bottom P x → is-initial (poset→precategory P) x
  is-bottom→is-initial is-bot x .fst   = is-bot x
  is-bottom→is-initial is-bot x .snd _ = ≤-thin _ _

  is-initial→is-bottom : ∀ {x} → is-initial (poset→precategory P) x → is-bottom P x
  is-initial→is-bottom initial x = initial x .fst

  is-bottom≃is-initial : ∀ {x} → is-bottom P x ≃ is-initial (poset→precategory P) x
  is-bottom≃is-initial = is-bottom→is-initial , biimp-is-equiv! _ is-initial→is-bottom
