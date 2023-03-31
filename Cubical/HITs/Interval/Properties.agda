{-# OPTIONS --safe #-}
module Cubical.HITs.Interval.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.Interval.Base

private variable
  ℓ : Level
  A : Type ℓ

isContrInterval : isContr Interval
isContrInterval = (zero , (λ x → rem x))
  where
  rem : (x : Interval) → zero ≡ x
  rem zero      = refl
  rem one       = seg
  rem (seg i) j = seg (i ∧ j)

funExtInterval : (A B : Type ℓ) (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g
funExtInterval A B f g p = λ i x → hmtpy x (seg i)
  where
  hmtpy : A → Interval → B
  hmtpy x zero    = f x
  hmtpy x one     = g x
  hmtpy x (seg i) = p x i

-- Note that this is not definitional (it is not proved by refl)
intervalEta : (f : Interval → A) → elim _ (f zero) (f one) (λ i → f (seg i)) ≡ f
intervalEta f i zero    = f zero
intervalEta f i one     = f one
intervalEta f i (seg j) = f (seg j)

externalIntervalFunctionsArePaths : (I → A) ≃ (Σ[ x ꞉ A ] Σ[ y ꞉ A ] x ≡ y)
externalIntervalFunctionsArePaths = isoToEquiv (iso (λ f → _ , _ , λ i → f i) (λ (_ , _ , p) i → p i) (λ (_ , _ , _) → refl) (λ _ → refl))

internalIntervalFunctionsArePaths : (Interval → A) ≃ (Σ[ x ꞉ A ] Σ[ y ꞉ A ] x ≡ y)
internalIntervalFunctionsArePaths = isoToEquiv (iso to from (λ _ → refl) (λ _ → funExt li′))
  where
  to : (Interval → A) → (Σ[ x ꞉ A ] Σ[ y ꞉ A ] x ≡ y)
  to f = f zero , f one , cong f seg

  from : Σ[ x ꞉ A ] Σ[ y ꞉ A ] (x ≡ y) → (i′ : Interval) → A
  from (x , y , p) zero = x
  from (x , y , p) one  = y
  from (x , y , p) (seg i) = p i

  li′ : ∀ {f} → (i′ : Interval) → from (to f) i′ ≡ f i′
  li′ zero    = refl
  li′ one     = refl
  li′ (seg _) = refl

observe : (I → A) ≃ (Interval → A)
observe = externalIntervalFunctionsArePaths ∙ₑ invEquiv internalIntervalFunctionsArePaths
