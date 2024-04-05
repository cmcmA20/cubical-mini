{-# OPTIONS --safe --backtracking-instance-search #-}
module Categories.Constructions.StrictCats where

open import Categories.Prelude
open import Categories.Strict

private variable
  o o′ h h′ : Level
  C : Precategory o h
  D : Precategory o′ h′

open Precategory

Functor-is-set : is-set (D .Ob) → is-set (Functor C D)
Functor-is-set {D} ds = ≅→is-of-hlevel! 2 functor-iso where instance
  DS : H-Level 2 (D .Ob)
  DS = hlevel-basic-instance 2 ds


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
