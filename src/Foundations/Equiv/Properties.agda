{-# OPTIONS --safe #-}
module Foundations.Equiv.Properties where

open import Foundations.Base
open import Foundations.Isomorphism
open import Foundations.HLevel

open import Foundations.Equiv.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  x y : A

_ₑ⁻¹ : A ≃ B → B ≃ A
e ₑ⁻¹ = Iso→Equiv (equiv→inverse (e .snd) , iso (e .fst) (equiv→unit (e .snd)) (equiv→counit (e .snd)))

sym-Equiv : (x ＝ y) ≃ (y ＝ x)
sym-Equiv = sym , is-iso→is-equiv (iso sym (λ _ → refl) (λ _ → refl))

is-contr→is-equiv : is-contr A → is-contr B
                  → {f : A → B} → is-equiv f
is-contr→is-equiv contr-A contr-B = is-iso→is-equiv f-is-iso where
  f-is-iso : is-iso _
  inv  f-is-iso _ = contr-A .fst
  rinv f-is-iso _ = is-contr→is-prop contr-B _ _
  linv f-is-iso _ = is-contr→is-prop contr-A _ _

is-contr→≃ : is-contr A → is-contr B → A ≃ B
is-contr→≃ contr-A contr-B = (λ _ → contr-B .fst) , is-iso→is-equiv f-is-iso where
  f-is-iso : is-iso _
  is-iso.inv f-is-iso _ = contr-A .fst
  is-iso.rinv f-is-iso _ = is-contr→is-prop contr-B _ _
  is-iso.linv f-is-iso _ = is-contr→is-prop contr-A _ _

module Equiv (e : A ≃ B) where
  to = e .fst
  from = equiv→inverse (e .snd)
  η = equiv→unit (e .snd)
  ε = equiv→counit (e .snd)
  zig = equiv→zig (e .snd)
  zag = equiv→zag (e .snd)

  injective : ∀ {x y} → to x ＝ to y → x ＝ y
  injective p = ap fst $ is-contr→is-prop (e .snd .equiv-proof _) (_ , refl) (_ , sym p)

  injective₂ : ∀ {x y z} → to x ＝ z → to y ＝ z → x ＝ y
  injective₂ p q = ap fst $ is-contr→is-prop (e .snd .equiv-proof _) (_ , p) (_ , q)

  inverse : B ≃ A
  inverse = e ₑ⁻¹


infixr 2 _≃⟨⟩_ _≃⟨_⟩_
infix  3 _≃∎

_≃⟨_⟩_ : (A : Type ℓ) → A ≃ B → B ≃ C → A ≃ C
_ ≃⟨ u ⟩ v = u ∙ₑ v

_≃⟨⟩_ : (A : Type ℓ) → A ≃ B → A ≃ B
_ ≃⟨⟩ e = e

_≃∎ : (A : Type ℓ) → A ≃ A
_ ≃∎ = idₑ

prop-extₑ : is-prop A → is-prop B
          → (A → B) → (B → A)
          → A ≃ B
prop-extₑ A-prop B-prop a→b b→a .fst = a→b
prop-extₑ A-prop B-prop a→b b→a .snd .equiv-proof y .fst = b→a y , B-prop _ _
prop-extₑ A-prop B-prop a→b b→a .snd .equiv-proof y .snd (p′ , path) =
  Σ-PathP (A-prop _ _) (to-PathP (is-prop→is-set B-prop _ _ _ _))
