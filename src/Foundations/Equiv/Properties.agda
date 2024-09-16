{-# OPTIONS --safe #-}
module Foundations.Equiv.Properties where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Path.Base
open import Foundations.Path.Groupoid
open import Foundations.Path.Reasoning
open import Foundations.Univalence

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  D : Type ℓ‴
  x y : A

instance
  Dual-≃ : Dual (_≃_ {ℓ} {ℓ′}) _≃_
  Dual-≃ ._ᵒᵖ (f , e) = ≅→≃ $ iso (is-equiv→inverse e) f
    (fun-ext $ is-equiv→unit e)
    (fun-ext $ is-equiv→counit e)

module _ (e : A ≃ B) where
  private
    f : A → B
    f = e .fst
    g : B → A
    g = e ⁻¹ $_

    η : id ＝ g ∘ f
    η = sym $ fun-ext (is-equiv→unit (e .snd))

    ε : f ∘ g ＝ id
    ε = fun-ext (is-equiv→counit (e .snd))

    zig : (x : A) → ap f (η # x) ∙ ε # f x ＝ refl
    zig x =
      ap f (η # x) ∙ ε # (f x)  ~⟨ ap sym (is-equiv→zig (e .snd) x) ▷ ε # (f x) ⟩
      ε # (f x) ⁻¹ ∙ ε # (f x)  ~⟨ ∙-inv-o (ε # f x) ⟩
      the (f x ＝ f x) refl     ∎

    zag : (y : B) → η # g y ∙ ap g (ε # y) ＝ refl
    zag y =
      η # (g y) ∙ ap g (ε # y)  ~⟨ η # (g y) ◁ is-equiv→zag (e .snd) y ⟩
      η # (g y) ∙ η # (g y) ⁻¹  ~⟨ ∙-inv-i (η # g y) ⟩
      the (g y ＝ g y) refl     ∎

  ≃→⊣ : (e $_) ⊣ (e ⁻¹ $_)
  ≃→⊣ .Adjoint.η = η
  ≃→⊣ .Adjoint.ε = ε
  ≃→⊣ .Adjoint.zig = zig
  ≃→⊣ .Adjoint.zag = zag

-- TODO generalize to arbitrary iso
≅ₜ→⊣ : (i : A ≅ B) → i .Iso.to ⊣ i .Iso.from
≅ₜ→⊣ i = ≃→⊣ (≅→≃ i)


module Equiv (e : A ≃ B) where
  to = e .fst
  from = is-equiv→inverse (e .snd)

  open Adjoint (≃→⊣ e) public

  zig′ : (x : A) → ap to (η # x) ⁻¹ ＝ ε # to x
  zig′ = is-equiv→zig (e .snd)

  zag′ : (y : B) → ap from (ε # y) ＝ η # from y ⁻¹
  zag′ = is-equiv→zag (e .snd)

  opaque
    injective : ∀ {x y} → to x ＝ to y → x ＝ y
    injective p = ap fst $ is-contr→is-prop (e .snd .equiv-proof _) (_ , refl) (_ , sym p)

    injective₂ : ∀ {x y z} → to x ＝ z → to y ＝ z → x ＝ y
    injective₂ p q = ap fst $ is-contr→is-prop (e .snd .equiv-proof _) (_ , p) (_ , q)

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
  GInvol-≃ : GInvol (_≃_ {ℓ} {ℓ′}) _≃_
  GInvol-≃ .invol _ = equiv-ext refl

  Comp-≃ : Comp (_≃_ {ℓ} {ℓ′}) (_≃_ {ℓ' = ℓ″}) _≃_
  Comp-≃ ._∙_  = _∙ₑ_

is-equiv-comp : {f : A → B} {g : B → C} → is-equiv f → is-equiv g → is-equiv (g ∘ f)
is-equiv-comp fe ge = ((_ , fe) ∙ (_ , ge)) .snd

inv-≃ : (A ≃ B) ≃ (B ≃ A)
inv-≃ = ≅→≃ $ iso _⁻¹ _⁻¹ (fun-ext invol) (fun-ext invol)

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
