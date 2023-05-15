{-# OPTIONS --safe #-}
module Structures.Product where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.Isomorphism
open import Foundations.Sigma.Properties
open import Foundations.Univalence

private variable
  ℓ ℓ₁ ℓ₂ : Level
  A : Type ℓ
  S T : Type ℓ → Type ℓ₁

Product-str : Structure ℓ S → Structure ℓ₂ T → Structure _ (λ X → S X × T X)
Product-str S T .is-hom (A , x , y) (B , x′ , y′) f =
  S .is-hom (A , x) (B , x′) f × T .is-hom (A , y) (B , y′) f

@0 Product-str-is-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                            → is-univalent σ → is-univalent τ
                            → is-univalent (Product-str σ τ)
Product-str-is-univalent {S} {T} {σ} {τ} θ₁ θ₂ {X , x , y} {Y , x′ , y′} f =
  (σ .is-hom (X , x) (Y , x′) _ × τ .is-hom (X , y) (Y , y′) _) ≃⟨ Σ-ap (θ₁ f) (λ _ → θ₂ f) ⟩
  (PathP _ _ _ × PathP _ _ _)                                   ≃⟨ Iso→Equiv Σ-PathP-iso ⟩
  PathP (λ i → S (ua f i) × T (ua f i)) (x , y) (x′ , y′)       ≃∎

Product-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X × T X)
Product-action actx acty eqv = Σ-ap (actx eqv) λ x → acty eqv

@0 Product-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (Product-action α β)
Product-action-is-transport α-tr β-tr e s =
  Σ-PathP (α-tr e (s .fst)) (β-tr e (s .snd))
