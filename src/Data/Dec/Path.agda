{-# OPTIONS --safe --no-exact-split #-}
module Data.Dec.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Unit.Base
open import Data.Reflects.Base as Reflects

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  b : Bool
  a₁ a₂ : A

yes-inj : yes a₁ ＝ yes a₂ → a₁ ＝ a₂
yes-inj {a₁} = ap (Dec.rec id λ _ → a₁)

instance
  Extensional-Dec : ⦃ sa : Extensional A ℓ′ ⦄ → Extensional (Dec A) ℓ′
  Extensional-Dec ⦃ sa ⦄ .Pathᵉ (_ because ofʸ p) (_ because ofʸ q) = Pathᵉ sa p q
  Extensional-Dec        .Pathᵉ (_ because ofⁿ _) (_ because ofⁿ _) = ⊤
  Extensional-Dec        .Pathᵉ _                 _                 = ⊥
  Extensional-Dec ⦃ sa ⦄ .reflᵉ (_ because ofʸ p) = reflᵉ sa p
  Extensional-Dec        .reflᵉ (_ because ofⁿ _) = _
  Extensional-Dec ⦃ sa ⦄ .idsᵉ .to-path {a = _ because ofʸ a} {b = _ because ofʸ b} =
    ap yes ∘ sa .idsᵉ .to-path
  Extensional-Dec        .idsᵉ .to-path {a = _ because ofⁿ a} {b = _ because ofⁿ _} _ =
    ap no prop!
  Extensional-Dec ⦃ sa ⦄ .idsᵉ .to-path-over {_ because ofʸ _} {_ because ofʸ _} =
    sa .idsᵉ .to-path-over
  Extensional-Dec        .idsᵉ .to-path-over {_ because ofⁿ _} {_ because ofⁿ _} _ = refl

opaque
  code-is-of-hlevel : {s₁ s₂ : Dec A} {n : HLevel}
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (1 + n) (Extensional-Dec .Pathᵉ s₁ s₂)
  code-is-of-hlevel {s₁ = yes a₁} {s₂ = yes a₂} A-hl = A-hl a₁ a₂
  code-is-of-hlevel {s₁ = yes a } {s₂ = no ¬a } _    = hlevel _
  code-is-of-hlevel {s₁ = no ¬a } {s₂ = yes a } _    = hlevel _
  code-is-of-hlevel {s₁ = no ¬a₁} {s₂ = no ¬a₂} _    = hlevel _

dec-is-contr : is-contr A → is-contr (Dec A)
dec-is-contr (a , _) .fst = yes a
dec-is-contr (a , p) .snd (no ¬a)  = false! (¬a a)
dec-is-contr (a , p) .snd (yes a′) = ap yes (p a′)

opaque
  dec-is-prop : is-prop A → is-prop (Dec A)
  dec-is-prop A-pr (yes a₁) (yes a₂) = ap yes (A-pr a₁ a₂)
  dec-is-prop A-pr (yes a ) (no ¬a ) = false! $ ¬a a
  dec-is-prop A-pr (no ¬a ) (yes a ) = false! $ ¬a a
  dec-is-prop A-pr (no ¬a₁) (no ¬a₂) = ap no prop!

dec-is-of-hlevel : (n : HLevel) → is-of-hlevel n A → is-of-hlevel n (Dec A)
dec-is-of-hlevel 0 = dec-is-contr
dec-is-of-hlevel 1 = dec-is-prop
dec-is-of-hlevel (suc (suc n)) A-hl s₁ s₂ =
  ≃→is-of-hlevel (1 + n) (identity-system-gives-path (Extensional-Dec .idsᵉ) ⁻¹)
    (code-is-of-hlevel {s₁ = s₁} {s₂ = s₂} A-hl)

instance
  H-Level-Dec : ∀ {n} → ⦃ H-Level n A ⦄ → H-Level n (Dec A)
  H-Level-Dec .H-Level.has-of-hlevel = dec-is-of-hlevel _ (hlevel _)
  {-# OVERLAPPING H-Level-Dec #-}

instance
  Reflects-yes≠no : {a : A} {¬a : ¬ A} → Reflects (yes a ＝ no ¬a) false
  Reflects-yes≠no = ofⁿ (λ p → subst (Dec.rec (λ _ → ⊤) λ _ → ⊥) p tt)

  Reflects-no≠yes : {a : A} {¬a : ¬ A} → Reflects (no ¬a ＝ yes a) false
  Reflects-no≠yes = reflects-sym auto

  Reflects-no=no : {p q : ¬ A} → Reflects (no p ＝ no q) true
  Reflects-no=no = ofʸ (ap no prop!)

  Reflects-yes=yes : {a₁ a₂ : A} ⦃ r : Reflects (a₁ ＝ a₂) b ⦄ → Reflects (yes a₁ ＝ yes a₂) b
  Reflects-yes=yes = Reflects.dmap (ap yes) (contra yes-inj) auto
