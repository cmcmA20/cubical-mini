{-# OPTIONS --safe #-}
module Foundations.Equiv.Properties where

open import Foundations.Base
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Univalence.Base

open import Foundations.Equiv.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  x y : A

_ₑ⁻¹ : A ≃ B → B ≃ A
e ₑ⁻¹ = Iso→Equiv (is-equiv→inverse (e .snd) , iso (e .fst) (is-equiv→unit (e .snd)) (is-equiv→counit (e .snd)))

open is-iso

inv-equiv-is-equiv : is-equiv (λ (e : A ≃ B) → e ₑ⁻¹)
inv-equiv-is-equiv = is-iso→is-equiv goal where
  goal : is-iso _ₑ⁻¹
  goal .inv  = _ₑ⁻¹
  goal .rinv _ = Equiv-ext refl
  goal .linv _ = Equiv-ext refl

-- TODO need half-adjoint equivalences
-- isEquivCong : {x y : A} (e : A ≃ B) → is-equiv (λ (p : x ＝ y) → cong (e .fst) p)
-- isEquivCong e = is-iso→is-equiv (congIso (equivToIso e))

-- congEquiv : {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (equivFun e x ≡ equivFun e y)
-- congEquiv e = isoToEquiv (congIso (equivToIso e))

-- isEquivPreComp : (e : A ≃ B) → isEquiv (λ (φ : B → C) → φ ∘ equivFun e)
-- isEquivPreComp e = snd (equiv→ (invEquiv e) (idEquiv _))

-- preCompEquiv : (e : A ≃ B) → (B → C) ≃ (A → C)
-- preCompEquiv e = (λ φ → φ ∘ fst e) , isEquivPreComp e

-- isEquivPostComp : (e : A ≃ B) → isEquiv (λ (φ : C → A) → e .fst ∘ φ)
-- isEquivPostComp e = snd (equivΠCod (λ _ → e))

-- postCompEquiv : (e : A ≃ B) → (C → A) ≃ (C → B)
-- postCompEquiv e = _ , isEquivPostComp e

@0 ap-≃ : (F : Type ℓ → Type ℓ′) → (A ≃ B) → F A ≃ F B
ap-≃ F e = path→Equiv (ap F (ua e))

sym-Equiv : (x ＝ y) ≃ (y ＝ x)
sym-Equiv = sym , is-iso→is-equiv (iso sym (λ _ → refl) (λ _ → refl))

is-contr→is-equiv : is-contr A → is-contr B
                  → {f : A → B} → is-equiv f
is-contr→is-equiv contr-A contr-B = is-iso→is-equiv f-is-iso where
  f-is-iso : is-iso _
  f-is-iso .inv  _ = contr-A .fst
  f-is-iso .rinv _ = is-contr→is-prop contr-B _ _
  f-is-iso .linv _ = is-contr→is-prop contr-A _ _

is-contr→≃ : is-contr A → is-contr B → A ≃ B
is-contr→≃ contr-A contr-B = (λ _ → contr-B .fst) , is-iso→is-equiv f-is-iso where
  f-is-iso : is-iso _
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
  Σ-path (A-prop _ _) (is-prop→is-set B-prop _ _ _ _)

module @0 ua {ℓ} {A B : Type ℓ} = Equiv (ua {A = A} {B} , univalence⁻¹)
