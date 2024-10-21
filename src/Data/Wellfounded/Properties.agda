{-# OPTIONS --safe #-}
module Data.Wellfounded.Properties where

open import Meta.Prelude

open import Data.Wellfounded.Base
open import Data.Empty.Base

private variable
  ℓa ℓb ℓ ℓ′ : Level
  A : 𝒰 ℓa
  B : 𝒰 ℓb
  _<_ : A → A → 𝒰 ℓ

Acc-on : (f : B → A) (b : B)
       → Acc _<_ (f b) → Acc (λ x y → f x < f y) b
Acc-on f b (acc rec) = acc λ y p → Acc-on f y (rec (f y) p)

-- well-foundedness

Wf→irr : Wf _<_ → ∀ x → ¬ x < x
Wf→irr {_<_} wf =
  to-induction wf (λ z → ¬ z < z)
    λ x ih x<x → ih x x<x x<x

Wf→asym : Wf _<_ → ∀ x y → x < y → ¬ y < x
Wf→asym {_<_} wf =
  to-induction wf (λ z → ∀ y → z < y → ¬ y < z)
    λ x ih y x<y y<x → ih y y<x x y<x x<y

Wf-mono : {_<′_ : A → A → 𝒰 ℓ′}
        → (∀ a b → a <′ b → a < b)
        → Wf _<_ → Wf _<′_
Wf-mono {_<′_} h wf =
  to-induction wf (Acc _<′_)
    λ x ih → acc λ y y<′x → ih y (h y x y<′x)

Wf-on : (f : B → A)
      → Wf _<_ → Wf (λ x y → f x < f y)
Wf-on f wf x = Acc-on f x (wf (f x))

-- Noetherianness

Noeth→irr : Noeth _<_ → ∀ x → ¬ x < x
Noeth→irr {_<_} nth =
  to-ninduction nth (λ z → ¬ z < z)
    λ x ih x<x → ih x x<x x<x

Noeth→asym : Noeth _<_ → ∀ x y → x < y → ¬ y < x
Noeth→asym {_<_} nth =
  to-ninduction nth (λ z → ∀ y → z < y → ¬ y < z)
    λ x ih y x<y y<x → ih y x<y x y<x x<y

Noeth-mono : {_<′_ : A → A → 𝒰 ℓ′}
           → (∀ a b → a <′ b → a < b)
           → Noeth _<_ → Noeth _<′_
Noeth-mono {_<′_} h nth =
  to-ninduction nth (Acc (flip _<′_))
    λ x ih → acc λ y x<′y → ih y (h x y x<′y)

Noeth-on : (f : B → A)
         → Noeth _<_ → Noeth (λ x y → f x < f y)
Noeth-on f nth x = Acc-on f x (nth (f x))

-- finite height

FinHeight-on : (f : B → A)
             → FinHeight _<_ → FinHeight (λ x y → f x < f y)
FinHeight-on f fh x = Acc-on f x (fh (f x) .fst) , Acc-on f x (fh (f x) .snd)
