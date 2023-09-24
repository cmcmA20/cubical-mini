{-# OPTIONS --safe #-}
module Foundations.Equiv.Properties where

open import Foundations.Base
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Path.Reasoning
open import Foundations.Univalence.Base

open import Foundations.Equiv.Base

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴
  x y : A

_ₑ⁻¹ : A ≃ B → B ≃ A
e ₑ⁻¹ = iso→equiv (is-equiv→inverse (e .snd) , iso (e .fst) (is-equiv→unit (e .snd)) (is-equiv→counit (e .snd)))
infix 90 _ₑ⁻¹

open is-iso

infixr 30 _∙ₑ_
_∙ₑ_ : A ≃ B → B ≃ C → A ≃ C
(f , fe) ∙ₑ (g , ge) = g ∘′ f , e where
  fi = is-equiv→is-iso fe
  f⁻¹ = fi .inv

  gi = is-equiv→is-iso ge
  g⁻¹ = gi .inv

  opaque
    right : (f⁻¹ ∘ g⁻¹) is-right-inverse-of (g ∘ f)
    right _ = ap g (fi .rinv _) ∙ gi .rinv _

    left : (f⁻¹ ∘ g⁻¹) is-left-inverse-of (g ∘ f)
    left _ = ap f⁻¹ (gi .linv _) ∙ fi .linv _

  e : is-equiv (g ∘′ f)
  e = is-iso→is-equiv $ iso (f⁻¹ ∘ g⁻¹) right left

is-equiv-comp : {f : A → B} {g : B → C} → is-equiv f → is-equiv g → is-equiv (g ∘ f)
is-equiv-comp fe ge = ((_ , fe) ∙ₑ (_ , ge)) .snd

inv-equiv-is-equiv : is-equiv (λ (e : A ≃ B) → e ₑ⁻¹)
inv-equiv-is-equiv = is-iso→is-equiv goal where
  goal : is-iso _ₑ⁻¹
  goal .inv  = _ₑ⁻¹
  goal .rinv _ = equiv-ext refl
  goal .linv _ = equiv-ext refl

is-equiv-inv : {f : A → B} (fe : is-equiv f) → is-equiv (is-equiv→inverse fe)
is-equiv-inv fe = ((_ , fe) ₑ⁻¹) .snd

@0 ap-≃ : (F : Type ℓ → Type ℓ′) → (A ≃ B) → F A ≃ F B
ap-≃ F e = path→equiv (ap F (ua e))

sym-equiv : (x ＝ y) ≃ (y ＝ x)
sym-equiv .fst = sym
sym-equiv .snd .equiv-proof = strict-contr-fibres sym

opaque
  unfolding is-of-hlevel
  is-contr→is-equiv : is-contr A → is-contr B
                    → {f : A → B} → is-equiv f
  is-contr→is-equiv contr-A contr-B {f} = is-iso→is-equiv f-is-iso where
    f-is-iso : is-iso f
    f-is-iso .inv  _ = contr-A .fst
    f-is-iso .rinv _ = is-contr→is-prop contr-B _ _
    f-is-iso .linv _ = is-contr→is-prop contr-A _ _

  is-contr→equiv : is-contr A → is-contr B → A ≃ B
  is-contr→equiv {A} contr-A contr-B = (λ _ → contr-B .fst) , is-iso→is-equiv f-is-iso where
    f-is-iso : is-iso {A = A} (λ _ → contr-B .fst)
    f-is-iso .inv  _ = contr-A .fst
    f-is-iso .rinv _ = is-contr→is-prop contr-B _ _
    f-is-iso .linv _ = is-contr→is-prop contr-A _ _

module Equiv (e : A ≃ B) where
  to = e .fst
  from = is-equiv→inverse (e .snd)
  η = is-equiv→unit (e .snd)
  ε = is-equiv→counit (e .snd)
  zig = is-equiv→zig (e .snd)
  zag = is-equiv→zag (e .snd)

  opaque
    unfolding is-of-hlevel
    injective : ∀ {x y} → to x ＝ to y → x ＝ y
    injective p = ap fst $ is-contr→is-prop (e .snd .equiv-proof _) (_ , refl) (_ , sym p)

    injective₂ : ∀ {x y z} → to x ＝ z → to y ＝ z → x ＝ y
    injective₂ p q = ap fst $ is-contr→is-prop (e .snd .equiv-proof _) (_ , p) (_ , q)

  inverse : B ≃ A
  inverse = e ₑ⁻¹


infixr 1.5 _≃⟨⟩_ _≃⟨_⟩_ _≃˘⟨_⟩_
infix  1.9 _≃∎

_≃⟨_⟩_ : (A : Type ℓ) → A ≃ B → B ≃ C → A ≃ C
_ ≃⟨ u ⟩ v = u ∙ₑ v

_≃˘⟨_⟩_ : (A : Type ℓ) → B ≃ A → B ≃ C → A ≃ C
_ ≃˘⟨ u ⟩ v = (u ₑ⁻¹) ∙ₑ v

_≃⟨⟩_ : (A : Type ℓ) → A ≃ B → A ≃ B
_ ≃⟨⟩ e = e

_≃∎ : (A : Type ℓ) → A ≃ A
_ ≃∎ = idₑ

prop-extₑ : is-prop A → is-prop B
          → (A → B) → (B → A)
          → A ≃ B
prop-extₑ A-prop B-prop a→b b→a .fst = a→b
prop-extₑ A-prop B-prop a→b b→a .snd .equiv-proof y .fst = b→a y , is-prop-β B-prop _ _
prop-extₑ A-prop B-prop a→b b→a .snd .equiv-proof y .snd (p′ , path) =
  Σ-path (is-prop-β A-prop _ _) (is-set-β (is-prop→is-set B-prop) _ _ _ _)

module @0 ua {ℓ} {A B : Type ℓ} = Equiv (ua {A = A} {B} , univalence⁻¹)

lift-equiv : Lift ℓ′ A ≃ A
lift-equiv .fst = lower
lift-equiv .snd .equiv-proof = strict-contr-fibres lift
