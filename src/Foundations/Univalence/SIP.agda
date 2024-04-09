{-# OPTIONS --safe #-}
module Foundations.Univalence.SIP where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Isomorphism
open import Foundations.Sigma.Properties
open import Foundations.Transport

open import Foundations.Univalence.Base

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  S T : Type ℓ → Type ℓ′

record Structure {ℓ₁ ℓ₂} (ℓ₃ : _)
  (S : Type ℓ₁ → Type ℓ₂) : Type (ℓsuc (ℓ₁ ⊔ ℓ₃) ⊔ ℓ₂) where

  constructor HomT→Str
  field
    is-hom : (A B : Σ _ S) → (A .fst ≃ B .fst) → Type ℓ₃

open Structure public

Type-with : Structure ℓ″ S → Type _
Type-with {S} _ = Σ _ S

@0 is-univalent : Structure ℓ S → Type _
is-univalent {S} ι =
  ∀ {X Y}
  → (f : X .fst ≃ Y .fst)
  → ι .is-hom X Y f ≃ ＜ X .snd ／ (λ i → S (ua f i)) ＼ Y .snd ＞

-- σ-homomorphic equivalences
_≃[_]_ : Σ _ S → Structure ℓ S → Σ _ S → Type _
A ≃[ σ ] B = Σ[ f ꞉ A .fst ≃ B .fst ] (σ .is-hom A B f)

private variable
  σ : Structure ℓ S

-- The Structure Identity Principle says that, if `S` is a `univalent
-- structure`, then the path space of `Σ S` is equivalent to the space of
-- S-homomorphic equivalences of types. Using groups as a grounding
-- example: identification of groups is group isomorphism.
@0 SIP : is-univalent σ → {X Y : Σ _ S}
       → (X ≃[ σ ] Y) ≃ (X ＝ Y)
SIP {S} {σ} is-univ {X} {Y} =
  X ≃[ σ ] Y                                                          ≃⟨⟩
  Σ[ e ꞉ X .fst ≃  Y .fst ] (σ .is-hom X Y e)                         ≃⟨ Σ-ap (ua , univalence⁻¹) is-univ ⟩
  Σ[ p ꞉ X .fst ＝ Y .fst ] ＜ X .snd ／ (λ i → S (p i)) ＼ Y .snd ＞ ≃⟨ ≅→≃ Σ-pathᴾ-iso ⟩
  X ＝ Y                                                              ≃∎

@0 sip : is-univalent σ → {X Y : Σ _ S} → (X ≃[ σ ] Y) → (X ＝ Y)
sip is-univ = SIP is-univ .fst

Equiv-action : (S : Type ℓ → Type ℓ′) → Type _
Equiv-action {ℓ} S = {X Y : Type ℓ} → (X ≃ Y) → (S X ≃ S Y)

action→structure : Equiv-action S → Structure _ S
action→structure act .is-hom (A , x) (B , y) f = act f .fst x ＝ y

@0 is-transport-str : {S : Type ℓ → Type ℓ′} → Equiv-action S → Type _
is-transport-str {ℓ} {S} act =
  {X Y : Type ℓ} (e : X ≃ Y) (s : S X) → act e .fst s ＝ subst S (ua e) s

preserves-id : {S : Type ℓ → Type ℓ} → Equiv-action S → Type _
preserves-id {ℓ} {S} act =
  {X : Type ℓ} (s : S X) → act idₑ .fst s ＝ s

@0 preserves-id→is-transport-str
  : (σ : Equiv-action S)
  → preserves-id σ → is-transport-str σ
preserves-id→is-transport-str {S} σ pres-id e s =
  Jₑ (λ _ e → σ e .fst s ＝ subst S (ua e) s) lemma′ e where
    lemma′ : σ idₑ .fst s ＝ subst S (ua idₑ) s
    lemma′ = sym $
      subst S (ua idₑ) s ＝⟨ ap (λ p → subst S p s) ua-idₑ ⟩
      transport refl s   ＝⟨ transport-refl _ ⟩
      s                  ＝⟨ sym (pres-id s) ⟩
      σ idₑ .fst s       ∎

@0 sym-transport-str
  : (α : Equiv-action S) (τ : is-transport-str α)
    {X Y : Type ℓ} (e : X ≃ Y) (t : S Y)
  → is-equiv→inverse (α e .snd) t ＝ subst S (sym (ua e)) t
sym-transport-str {S} α τ e t =
     sym (transport⁻-transport (ap S (ua e)) (from t))
  ∙∙ sym (ap (subst S (sym (ua e))) (τ e (from t)))
  ∙∙ ap (subst S (sym (ua e))) (ε t)
  where open module ae = Equiv (α e)

@0 is-transport→is-univalent : (a : Equiv-action S)
                             → is-transport-str a
                             → is-univalent (action→structure a)
is-transport→is-univalent {S} act is-tr {X , s} {Y , t} eqv =
  act eqv .fst s ＝ t                  ≃⟨ ＝→≃ (ap (_＝ t) (is-tr eqv s)) ⟩
  subst S (ua eqv) s ＝ t              ≃⟨ ＝→≃ (sym (pathᴾ＝path (λ i → S (ua eqv i)) s t)) ⟩
  ＜ s ／ (λ i → S (ua eqv i)) ＼ t ＞ ≃∎
