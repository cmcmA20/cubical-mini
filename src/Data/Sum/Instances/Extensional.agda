{-# OPTIONS --safe #-}
module Data.Sum.Instances.Extensional where

open import Foundations.Base

open import Meta.Extensionality

open import Data.Empty.Base
open import Data.Sum.Base

-- TODO check if it's really useful
Extensional-⊎
  : ∀ {ℓ ℓ′ ℓr ℓs} {A : Type ℓ} {B : Type ℓ′}
  → ⦃ sa : Extensional A ℓr ⦄
  → ⦃ sb : Extensional B ℓs ⦄
  → Extensional (A ⊎ B) (ℓr ⊔ ℓs)
Extensional-⊎ {ℓs} ⦃ sa ⦄ .Pathᵉ (inl x) (inl x′) = Lift ℓs (Pathᵉ sa x x′)
Extensional-⊎ {ℓr} ⦃ sb ⦄ .Pathᵉ (inr y) (inr y′) = Lift ℓr (Pathᵉ sb y y′)
Extensional-⊎ .Pathᵉ _ _ = Lift _ ⊥
Extensional-⊎ ⦃ sa ⦄ .reflᵉ (inl x) = lift (reflᵉ sa x)
Extensional-⊎ ⦃ sb ⦄ .reflᵉ (inr y) = lift (reflᵉ sb y)
Extensional-⊎ ⦃ sa ⦄ .idsᵉ .to-path {inl x} {inl x′} (lift p) = ap inl $ sa .idsᵉ .to-path p
Extensional-⊎ ⦃ sb ⦄ .idsᵉ .to-path {inr y} {inr y′} (lift p) = ap inr $ sb .idsᵉ .to-path p
Extensional-⊎ ⦃ sa ⦄ .idsᵉ .to-path-over {inl x} {inl x′} (lift p) = apP (λ _ → lift) $ sa .idsᵉ .to-path-over p
Extensional-⊎ ⦃ sb ⦄ .idsᵉ .to-path-over {inr y} {inr y′} (lift p) = apP (λ _ → lift) $ sb .idsᵉ .to-path-over p

instance
  extensionality-⊎
    : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    → Extensionality (A ⊎ B)
  extensionality-⊎ .Extensionality.lemma = quote Extensional-⊎
