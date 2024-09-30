{-# OPTIONS --safe #-}
module Cat.Constructions.StrictCats where

open import Cat.Prelude
open import Cat.Strict

private variable
  o o′ h h′ : Level
  C : Precategory o h
  D : Precategory o′ h′

open Precategory

Functor-is-set
  : ⦃ ds : H-Level 2 (D .Ob) ⦄ ⦃ dhs : ∀ {x y} → H-Level 2 (D .Hom x y) ⦄
  → is-set (C ⇒ D)
Functor-is-set {D} ⦃ dhs ⦄ = ≅→is-of-hlevel 2 functor-iso
  $ Σ-is-of-hlevel 2 (hlevel 2) λ f → Σ-is-of-hlevel 2 (hlevel 2) λ g
  → Σ-is-of-hlevel 2 (is-prop→is-set (hlevel 1)) λ _ → is-prop→is-set (hlevel 1)

-- TODO
-- Strict-cats : ∀ o h → Precategory _ _
-- Strict-cats o h .Ob = Σ[ C ꞉ Precategory o h ] is-strict C
-- Strict-cats o h .Hom (C , _) (D , _) = Functor C D
-- Strict-cats o h .id  = Id
-- Strict-cats o h ._∘_ = _∘ᶠ_
-- Strict-cats o h .id-r _      = {!!} -- Functor-path (λ _ → refl) λ _ → refl
-- Strict-cats o h .id-l _      = {!!} -- Functor-path (λ _ → refl) λ _ → refl
-- Strict-cats o h .assoc _ _ _ = {!!} -- Functor-path (λ _ → refl) λ _ → refl
-- Strict-cats o h .Hom-set _ (_ , ds) = Functor-is-set ds
