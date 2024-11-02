{-# OPTIONS --safe #-}
module Data.Maybe.Instances.Idiom where

open import Foundations.Base

open import Meta.Effect.Base
open import Meta.Effect.Idiom
open import Meta.Effect.Map

open import Data.Maybe.Base
open import Data.Maybe.Instances.Map public

private variable
  ℓ : Level
  A B C : Type ℓ

_<*>ₘ_ : Maybe (A → B) → Maybe A → Maybe B
nothing <*>ₘ _  = nothing
just f  <*>ₘ mx = mapₘ f mx

instance
  Idiom-Maybe : Idiom (eff Maybe)
  Idiom-Maybe .pure = just
  Idiom-Maybe ._<*>_ = _<*>ₘ_

  Lawful-Idiom-Maybe : Lawful-Idiom (eff Maybe)
  Lawful-Idiom-Maybe .pure-id {A} {v} = go v  where opaque
    go : (mx : Maybe A) → map refl mx ＝ mx
    go (just x) = refl
    go nothing  = refl
  Lawful-Idiom-Maybe .pure-pres-app = refl
  Lawful-Idiom-Maybe .pure-interchange {A} {B} {u} {v} = go u v where opaque
    go : (mf : Maybe (A → B)) (x : A) → (mf <*> pure x) ＝ (pure (_$ x) <*> mf)
    go (just f) x = refl
    go nothing  _ = refl
  Lawful-Idiom-Maybe .pure-comp {A} {B} {C} {u} {v} {w} = go u v w where opaque
    go : (mg : Maybe (B → C)) (mf : Maybe (A → B)) (mx : Maybe A)
       → (pure _∘ˢ_ <*> mg <*> mf <*> mx) ＝ (mg <*> (mf <*> mx))
    go (just g) (just f) (just x) = refl
    go (just g) (just f) nothing  = refl
    go (just g) nothing  mx       = refl
    go nothing  _        _        = refl
