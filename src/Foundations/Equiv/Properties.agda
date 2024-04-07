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
e ₑ⁻¹ = ≅→≃ (is-equiv→inverse (e .snd) , iso (e .fst) (is-equiv→unit (e .snd)) (is-equiv→counit (e .snd)))
infix 90 _ₑ⁻¹

open is-iso

infixr 30 _∙ₑ_
_∙ₑ_ : A ≃ B → B ≃ C → A ≃ C
(f , fe) ∙ₑ (g , ge) = g ∘ˢ f , e where
  fi = is-equiv→is-iso fe
  f⁻¹ = fi .inv

  gi = is-equiv→is-iso ge
  g⁻¹ = gi .inv

  opaque
    right : (f⁻¹ ∘ g⁻¹) is-right-inverse-of (g ∘ f)
    right _ = ap g (fi .rinv _) ∙ gi .rinv _

    left : (f⁻¹ ∘ g⁻¹) is-left-inverse-of (g ∘ f)
    left _ = ap f⁻¹ (gi .linv _) ∙ fi .linv _

  e : is-equiv (g ∘ˢ f)
  e = is-iso→is-equiv $ iso (f⁻¹ ∘ g⁻¹) right left

is-equiv-comp : {f : A → B} {g : B → C} → is-equiv f → is-equiv g → is-equiv (g ∘ f)
is-equiv-comp fe ge = ((_ , fe) ∙ₑ (_ , ge)) .snd

inv-equiv-is-equiv : is-equiv (λ (e : A ≃ B) → e ₑ⁻¹)
inv-equiv-is-equiv = is-iso→is-equiv goal where
  goal : is-iso _ₑ⁻¹
  goal .inv  = _ₑ⁻¹
  goal .rinv _ = equiv-ext refl
  goal .linv _ = equiv-ext refl

inv-≃ : (A ≃ B) ≃ (B ≃ A)
inv-≃ = _ , inv-equiv-is-equiv

is-equiv-inv : {f : A → B} (fe : is-equiv f) → is-equiv (is-equiv→inverse fe)
is-equiv-inv fe = ((_ , fe) ₑ⁻¹) .snd

-- action on equivalences by univalence
@0 generic-ae : (F : Type ℓ → Type ℓ′) → A ≃ B → F A ≃ F B
generic-ae F e = ＝→≃ (ap F (ua e))


sym-≃ : (x ＝ y) ≃ (y ＝ x)
sym-≃ .fst = sym
sym-≃ .snd .equiv-proof = strict-contr-fibres sym

is-contr→is-equiv : is-contr A → is-contr B
                  → {f : A → B} → is-equiv f
is-contr→is-equiv contr-A contr-B {f} = is-iso→is-equiv f-is-iso where
  f-is-iso : is-iso f
  f-is-iso .inv  _ = contr-A .fst
  f-is-iso .rinv _ = is-contr→is-prop contr-B _ _
  f-is-iso .linv _ = is-contr→is-prop contr-A _ _

is-contr→≃ : is-contr A → is-contr B → A ≃ B
is-contr→≃ {A} contr-A contr-B = (λ _ → contr-B .fst) , is-iso→is-equiv f-is-iso where
  f-is-iso : is-iso {A = A} (λ _ → contr-B .fst)
  f-is-iso .inv  _ = contr-A .fst
  f-is-iso .rinv _ = is-contr→is-prop contr-B _ _
  f-is-iso .linv _ = is-contr→is-prop contr-A _ _

is-equiv→pre-is-equiv : {f : A → B} → is-equiv f → is-equiv {A = C → A} (f ∘_)
is-equiv→pre-is-equiv {f} f-eqv = is-iso→is-equiv isiso where
  f-iso : is-iso f
  f-iso = is-equiv→is-iso f-eqv

  f⁻¹ : _
  f⁻¹ = f-iso .is-iso.inv

  isiso : is-iso (_∘_ f)
  isiso .is-iso.inv f x = f⁻¹ (f x)
  isiso .is-iso.rinv f = fun-ext λ _ → f-iso .is-iso.rinv _
  isiso .is-iso.linv f = fun-ext λ _ → f-iso .is-iso.linv _

is-equiv→post-is-equiv : {f : A → B} → is-equiv f → is-equiv {A = B → C} (_∘ f)
is-equiv→post-is-equiv {f} f-eqv = is-iso→is-equiv isiso where
  f-iso : is-iso f
  f-iso = is-equiv→is-iso f-eqv

  f⁻¹ : _
  f⁻¹ = f-iso .is-iso.inv

  isiso : is-iso _
  isiso .is-iso.inv f x = f (f⁻¹ x)
  isiso .is-iso.rinv f = fun-ext λ x → ap f (f-iso .is-iso.linv _)
  isiso .is-iso.linv f = fun-ext λ x → ap f (f-iso .is-iso.rinv _)

module Equiv (e : A ≃ B) where
  to = e .fst
  from = is-equiv→inverse (e .snd)
  η = is-equiv→unit (e .snd)
  ε = is-equiv→counit (e .snd)
  zig = is-equiv→zig (e .snd)
  zag = is-equiv→zag (e .snd)

  opaque
    injective : ∀ {x y} → to x ＝ to y → x ＝ y
    injective p = ap fst $ is-contr→is-prop (e .snd .equiv-proof _) (_ , refl) (_ , sym p)

    injective₂ : ∀ {x y z} → to x ＝ z → to y ＝ z → x ＝ y
    injective₂ p q = ap fst $ is-contr→is-prop (e .snd .equiv-proof _) (_ , p) (_ , q)

    adjunct-l : ∀ {x y} → to x ＝ y → x ＝ from y
    adjunct-l p = sym (η _) ∙ ap from p

    adjunct-r : ∀ {x y} → x ＝ from y → to x ＝ y
    adjunct-r p = ap to p ∙ ε _

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

lift≃id : Lift ℓ′ A ≃ A
lift≃id .fst = lower
lift≃id .snd .equiv-proof = strict-contr-fibres lift

module @0 ua {ℓ} {A B : Type ℓ} = Equiv (ua {A = A} {B} , univalence⁻¹)

module _
  (A-pr : is-prop A) (B-pr : is-prop B)
  (to : A → B) (from : B → A)
  where

  biimp-is-equiv : is-equiv to
  biimp-is-equiv .equiv-proof b .fst = from b , B-pr _ _
  biimp-is-equiv .equiv-proof b .snd (p′ , path) =
    Σ-path (A-pr _ _) (is-prop→is-set B-pr _ _ _ _)

  prop-extₑ : A ≃ B
  prop-extₑ .fst = to
  prop-extₑ .snd = biimp-is-equiv


-- Automation

biimp-is-equiv! : ⦃ A-pr : H-Level 1 A ⦄ ⦃ B-pr : H-Level 1 B ⦄
                → (to : A → B) → (B → A)
                → is-equiv to
biimp-is-equiv! = biimp-is-equiv (hlevel 1) (hlevel 1)

prop-extₑ! : ⦃ A-pr : H-Level 1 A ⦄ ⦃ B-pr : H-Level 1 B ⦄
           → (A → B) → (B → A)
           → A ≃ B
prop-extₑ! = prop-extₑ (hlevel 1) (hlevel 1)
