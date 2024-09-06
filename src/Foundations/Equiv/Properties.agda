{-# OPTIONS --safe #-}
module Foundations.Equiv.Properties where

open import Foundations.Base
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Path.Reasoning
open import Foundations.Univalence

open import Foundations.Equiv.Base

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴
  x y : A

instance
  Sym-≃ : Sym (_≃_ {ℓ} {ℓ′}) _≃_
  Sym-≃ .sym (f , e) = ≅→≃ $ iso (is-equiv→inverse e) f
    (fun-ext $ is-equiv→unit e)
    (fun-ext $ is-equiv→counit e)

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
  inverse = e ⁻¹

module @0 ua {ℓ} {A B : Type ℓ} = Equiv (ua {A = A} {B} , univalence⁻¹)

open is-invertible

infixr 30 _∙ₑ_
_∙ₑ_ : A ≃ B → B ≃ C → A ≃ C
(f , fe) ∙ₑ (g , ge) = f ∙ g , e where
  fi = is-equiv→is-inv fe
  gi = is-equiv→is-inv ge

  f⁻¹ = fi .inv
  g⁻¹ = gi .inv

  opaque
    s : (g⁻¹ ∙ f⁻¹) section-of (f ∙ g)
    s = (g⁻¹ ◁ fi .inv-o ▷ g) ∙ gi .inv-o

    r : (g⁻¹ ∙ f⁻¹) retract-of (f ∙ g)
    r = (f ◁ gi .inv-i ▷ f⁻¹) ∙ fi .inv-i

  e : is-equiv (f ∙ g)
  e = is-inv→is-equiv $ invertible (g⁻¹ ∙ f⁻¹) s r

instance
  Invol-≃ : Invol (_≃_ {ℓ} {ℓ′}) _≃_
  Invol-≃ .sym-invol _ = equiv-ext refl

  Trans-≃ : Trans (_≃_ {ℓ} {ℓ′}) (_≃_ {ℓ' = ℓ″}) _≃_
  Trans-≃ ._∙_  = _∙ₑ_

is-equiv-comp : {f : A → B} {g : B → C} → is-equiv f → is-equiv g → is-equiv (g ∘ f)
is-equiv-comp fe ge = ((_ , fe) ∙ (_ , ge)) .snd

inv-≃ : (A ≃ B) ≃ (B ≃ A)
inv-≃ = ≅→≃ $ iso _⁻¹ _⁻¹ (fun-ext sym-invol) (fun-ext sym-invol)

is-equiv-inv : {f : A → B} (fe : is-equiv f) → is-equiv (is-equiv→inverse fe)
is-equiv-inv fe = ((_ , fe) ⁻¹) .snd

-- action on equivalences by univalence
@0 generic-ae : (F : Type ℓ → Type ℓ′) → A ≃ B → F A ≃ F B
generic-ae F e = =→≃ (ap F (ua e))


sym-≃ : (x ＝ y) ≃ (y ＝ x)
sym-≃ .fst = sym
sym-≃ .snd .equiv-proof = strict-contr-fibres sym

is-contr→is-equiv : is-contr A → is-contr B
                  → {f : A → B} → is-equiv f
is-contr→is-equiv contr-A contr-B {f} = is-inv→is-equiv $ invertible
  (λ _ → contr-A .fst)
  (fun-ext λ _ → is-contr→is-prop contr-B _ _)
  (fun-ext λ _ → is-contr→is-prop contr-A _ _)

is-contr→≃ : is-contr A → is-contr B → A ≃ B
is-contr→≃ {A} contr-A contr-B = (λ _ → contr-B .fst) , is-contr→is-equiv contr-A contr-B

is-equiv→pre-is-equiv : {f : A → B} → is-equiv f → is-equiv {A = C → A} (_∙ f) -- (f ∘_)
is-equiv→pre-is-equiv {f} f-eqv = is-inv→is-equiv $ invertible (_∙ f⁻¹)
  (fun-ext $ _◁ fi .inv-o)
  (fun-ext $ _◁ fi .inv-i)
    where
    fi = is-equiv→is-inv f-eqv
    f⁻¹ = fi .inv

is-equiv→post-is-equiv : {f : A → B} → is-equiv f → is-equiv {A = B → C} (f ∙_) -- (_∘ f)
is-equiv→post-is-equiv {f} f-eqv = is-inv→is-equiv $ invertible (f⁻¹ ∙_)
  (fun-ext $ fi .inv-i ▷_)
  (fun-ext $ fi .inv-o ▷_)
    where
    fi = is-equiv→is-inv f-eqv
    f⁻¹ = fi .inv

lift≃id : Lift ℓ′ A ≃ A
lift≃id .fst = lower
lift≃id .snd .equiv-proof = strict-contr-fibres lift

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
