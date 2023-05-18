{-# OPTIONS --safe #-}
module Structures.Axiom where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.HLevel.Base
open import Foundations.Isomorphism
open import Foundations.Sigma.Properties
open import Foundations.Univalence

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Type ℓ
  S T : Type ℓ → Type ℓ₁

module _
  (σ : Structure ℓ S)
  (axioms : (X : _) → S X → Type ℓ₃)
  where

  Axiom-str : Structure ℓ (λ X → Σ[ s ꞉ S X ] (axioms X s))
  Axiom-str .is-hom (A , s , a) (B , t , b) f =
    σ .is-hom (A , s) (B , t) f

  module _
    (univ : is-univalent σ)
    (axioms-prop : ∀ {X} {s} → is-prop (axioms X s)) where

    @0 Axiom-str-univalent : is-univalent Axiom-str
    Axiom-str-univalent {X = A , s , a} {Y = B , t , b} f =
      σ .is-hom (A , s) (B , t) f
        ≃⟨ univ f ⟩
      ＜ s ／ (λ i → S (ua f i)) ＼ t ＞
        ≃⟨ Σ-contract (λ x → PathP-is-of-hlevel 0 (b , (axioms-prop b))) ₑ⁻¹ ⟩
      (Σ[ p ꞉ ＜ s ／ (λ i → S (ua f i)) ＼ t ＞ ] ＜ a ／ (λ i → axioms (ua f i) (p i)) ＼ b ＞)
        ≃⟨ Iso→Equiv Σ-PathP-iso ⟩
      _
        ≃∎

@0 transfer-axioms
  : {σ : Structure ℓ S} {univ : is-univalent σ}
    {axioms : (X : _) → S X → Type ℓ₃}
  → (A : Type-with (Axiom-str σ axioms)) (B : Type-with σ)
  → (A .fst , A .snd .fst) ≃[ σ ] B
  → axioms (B .fst) (B .snd)
transfer-axioms {univ} {axioms} A B eqv =
  subst (λ { (x , y) → axioms x y }) (sip univ eqv) (A .snd .snd)
