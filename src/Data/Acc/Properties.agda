{-# OPTIONS --safe #-}
module Data.Acc.Properties where

open import Meta.Prelude
open Variadics _

open import Data.Acc.Base
open import Data.Acc.Path
open import Data.Empty.Base

private variable
  ℓa ℓb ℓ ℓ′ : Level
  A : 𝒰 ℓa
  B : 𝒰 ℓb
  _<_ _<′_ : A → A → 𝒰 ℓ

acc-map : {_<_ : A → A → 𝒰 ℓ} {_<′_ : A → A → 𝒰 ℓ′}
       → Π[ _<′_ ⇒ _<_ ]
       → ∀ {x} → Acc _<_ x → Acc _<′_ x
acc-map h {x} (acc rec) =
  acc λ y y<′ → acc-map h (rec y (h y x y<′))

acc-flip-map : {_<_ : A → A → 𝒰 ℓ} {_<′_ : A → A → 𝒰 ℓ′}
       → Π[ _<′_ ⇒ _<_ ]
       → ∀ {x} → Acc (flip _<_) x → Acc (flip _<′_) x
acc-flip-map h {x} (acc rec) =
  acc λ y x<′ → acc-flip-map h (rec y (h x y x<′))

acc-lift : (f : B → A) (b : B)
         → Acc _<_ (f b) → Acc (λ x y → f x < f y) b
acc-lift f b (acc rec) = acc λ y p → acc-lift f y (rec (f y) p)


-- well-foundedness

wf→irrefl : is-wf _<_ → ∀ x → ¬ x < x
wf→irrefl {_<_} wf = to-induction wf (λ z → ¬ z < z)
  λ x ih x<x → ih x x<x x<x

wf→asym : is-wf _<_ → ∀ x y → x < y → ¬ y < x
wf→asym {_<_} wf = to-induction wf (λ z → ∀ y → z < y → ¬ y < z)
  λ x ih y x<y y<x → ih y y<x x y<x x<y

wf-map : {_<_ : A → A → 𝒰 ℓ} {_<′_ : A → A → 𝒰 ℓ′}
       → Π[ _<′_ ⇒ _<_ ]
       → is-wf _<_ → is-wf _<′_
wf-map {_<′_} h wf x = acc-map h (wf x)

wf-lift : (f : B → A)
        → is-wf _<_ → is-wf (λ x y → f x < f y)
wf-lift f wf x = acc-lift f x (wf (f x))

to-induction-acc-eq : {A : 𝒰 ℓa} {_<_ : A → A → 𝒰 ℓ}
                      (wf : is-wf _<_)
                    → (P : A → 𝒰 ℓ′)
                    → (ih : ∀ x → Π[ _< x ⇒ P ] → P x)
                    → ∀ x → (ax : Acc _<_ x)
                    → to-induction-acc P ih x ax
                    ＝ ih x λ y _ → to-induction-acc P ih y (wf y)
to-induction-acc-eq wf P ih x (acc a) =
  ap (ih x) $
  fun-ext λ y → fun-ext λ y<x →
  ap (to-induction-acc P ih y) $
  acc-is-prop y ((a y y<x)) (wf y)

to-induction-eq : {A : 𝒰 ℓa} {_<_ : A → A → 𝒰 ℓ}
                  (wf : is-wf _<_)
                → (P : A → 𝒰 ℓ′)
                → (ih : ∀ x → Π[ _< x ⇒ P ] → P x)
                → ∀ x
                → to-induction wf P ih x ＝ ih x λ y _ → to-induction wf P ih y
to-induction-eq wf P ih x = to-induction-acc-eq wf P ih x (wf x)

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
noeth-map {_<′_} h nth x = acc-flip-map h (nth x)

noeth-lift : (f : B → A)
           → is-noeth _<_ → is-noeth (λ x y → f x < f y)
noeth-lift f nth x = acc-lift f x (nth (f x))


-- finite height

finite-height-lift
  : (f : B → A)
  → is-of-finite-height _<_ → is-of-finite-height (λ x y → f x < f y)
finite-height-lift f fh x = acc-lift f x (fh (f x) .fst) , acc-lift f x (fh (f x) .snd)
