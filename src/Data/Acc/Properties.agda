{-# OPTIONS --safe #-}
module Data.Acc.Properties where

open import Meta.Prelude
open Variadics _

open import Data.Acc.Base
open import Data.Empty.Base

private variable
  ℓa ℓb ℓ ℓ′ : Level
  A : 𝒰 ℓa
  B : 𝒰 ℓb
  _<_ _<′_ : A → A → 𝒰 ℓ

acc-lift : (f : B → A) (b : B)
         → Acc _<_ (f b) → Acc (λ x y → f x < f y) b
acc-lift f b (acc rec) = acc λ y p → acc-lift f y (rec (f y) p)


-- well-foundedness

wf→irrefl : is-wf _<_ → ∀ x → ¬ x < x
wf→irrefl {_<_} wf = to-induction wf (λ z → ¬ z < z)
  λ x ih x<x → ih x x<x x<x

is-wf→asym : is-wf _<_ → ∀ x y → x < y → ¬ y < x
is-wf→asym {_<_} wf = to-induction wf (λ z → ∀ y → z < y → ¬ y < z)
  λ x ih y x<y y<x → ih y y<x x y<x x<y

wf-map : {_<_ : A → A → 𝒰 ℓ} {_<′_ : A → A → 𝒰 ℓ′}
       → Π[ _<′_ ⇒ _<_ ]
       → is-wf _<_ → is-wf _<′_
wf-map {_<′_} h wf =
  to-induction wf (Acc _<′_)
    λ x ih → acc λ y y<′x → ih y (h y x y<′x)

wf-lift : (f : B → A)
        → is-wf _<_ → is-wf (λ x y → f x < f y)
wf-lift f wf x = acc-lift f x (wf (f x))


-- Noetherianness

noeth→irrefl : is-noeth _<_ → ∀ x → ¬ x < x
noeth→irrefl {_<_} nth =
  to-ninduction nth (λ z → ¬ z < z)
    λ x ih x<x → ih x x<x x<x

noeth→asym : is-noeth _<_ → ∀ x y → x < y → ¬ y < x
noeth→asym {_<_} nth =
  to-ninduction nth (λ z → ∀ y → z < y → ¬ y < z)
    λ x ih y x<y y<x → ih y x<y x y<x x<y

noeth-map : {_<_ : A → A → 𝒰 ℓ} {_<′_ : A → A → 𝒰 ℓ′}
          → Π[ _<′_ ⇒ _<_ ]
          → is-noeth _<_ → is-noeth _<′_
noeth-map {_<′_} h nth =
  to-ninduction nth (Acc (flip _<′_))
    λ x ih → acc λ y x<′y → ih y (h x y x<′y)

noeth-lift : (f : B → A)
           → is-noeth _<_ → is-noeth (λ x y → f x < f y)
noeth-lift f nth x = acc-lift f x (nth (f x))


-- finite height

finite-height-lift
  : (f : B → A)
  → is-of-finite-height _<_ → is-of-finite-height (λ x y → f x < f y)
finite-height-lift f fh x = acc-lift f x (fh (f x) .fst) , acc-lift f x (fh (f x) .snd)
