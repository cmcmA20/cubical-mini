{-# OPTIONS --safe #-}
module Data.Maybe.Properties where

open import Meta.Prelude

open import Logic.Decidability

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Maybe.Base as Maybe public
open import Data.Maybe.Path
open import Data.Sum.Base
open import Data.Sum.Properties
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  x : Maybe A

rec-fusion : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
             {z : B} {f : A → B} {g : B → C}
             (xm : Maybe A)
           → g (Maybe.rec z f xm) ＝ Maybe.rec (g z) (g ∘ f) xm
rec-fusion (just x) = refl
rec-fusion nothing = refl

maybe-as-sum : Maybe A ≃ (⊤ ⊎ A)
maybe-as-sum = ≅→≃ i where
  open Iso
  i : _ ≅ _
  i .to (just x) = inr x
  i .to nothing = inl tt
  i .from (inl _) = nothing
  i .from (inr x) = just x
  i .inverses .Inverses.inv-o _ (inl _) = inl tt
  i .inverses .Inverses.inv-o _ (inr x) = inr x
  i .inverses .Inverses.inv-i j (just x) = just x
  i .inverses .Inverses.inv-i j nothing = nothing

fibre-just : (m : Maybe A) ⦃ _ : So (is-just? m) ⦄ → fibre just m
fibre-just (just x) = x , refl

maybe-is-of-size : is-of-size ℓ′ A → is-of-size ℓ′ (Maybe A)
maybe-is-of-size {ℓ′} {A} sz =
  ≃→is-of-size (maybe-as-sum ⁻¹) (⊎-is-of-size (size 0ℓ) sz)

instance
  Size-Maybe : {A : 𝒰 ℓ}
               ⦃ sa : Size ℓ′ A ⦄
             → Size ℓ′ (Maybe A)
  Size-Maybe {ℓ′} .Size.has-of-size = maybe-is-of-size (size ℓ′)
