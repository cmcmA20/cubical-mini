{-# OPTIONS --safe #-}
module Foundations.Equiv.Fibrewise where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.HLevel
open import Foundations.Isomorphism

-- Don't you ever try importing meta stuff here

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  P : A → Type ℓ′
  Q : A → Type ℓ″
  f : Π[ x ꞉ A ] (P x → Q x)

total : Π[ x ꞉ A ] (P x → Q x)
      → Σ A P → Σ A Q
total f (x , y) = x , f x y

total-fibres-equiv : {x : A} {v : Q x}
                   → fibre (f x)          v
                   ≃ fibre (total f) (x , v)
total-fibres-equiv {A} {Q} {f} = ≅→≃ $ to , iso from ri li where
  to : {x : A} {v : Q x} → fibre (f x) v → fibre (total f) (x , v)
  to (v′ , p) = (_ , v′) , λ i → _ , p i

  from : {x : A} {v : Q x} → fibre (total f) (x , v) → fibre (f x) v
  from ((x , v) , p) = transport (λ i → fibre (f (p i .fst)) (p i .snd)) (v , refl)

  opaque
    unfolding singleton-is-prop
    ri : {x : A} {v : Q x}
       → from {x = x} {v = v} is-right-inverse-of to
    ri ((x , v) , p) =
      J (λ { _ p → to (from ((x , v) , p)) ＝ ((x , v) , p) })
        (ap to (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl)))
        p

    li : {x : A} {v : Q x}
       → from {x = x} {v = v} is-left-inverse-of to
    li (v , p) =
      J (λ { _ p → from (to (v , p)) ＝ (v , p) })
        (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl))
        p

total-is-equiv→fibrewise-is-equiv : is-equiv (total f)
                                  → ∀[ x ꞉ A ] is-equiv (f x)
total-is-equiv→fibrewise-is-equiv eqv {x} .equiv-proof y = is-equiv→is-of-hlevel 0
  from (inverse .snd) (eqv .equiv-proof (x , y))
    where open Equiv total-fibres-equiv

fibrewise-is-equiv→total-is-equiv : ∀[ x ꞉ A ] is-equiv (f x)
                                  → is-equiv (total f)
fibrewise-is-equiv→total-is-equiv always-eqv .equiv-proof y = is-equiv→is-of-hlevel 0
  (total-fibres-equiv .fst) (total-fibres-equiv .snd)
  (always-eqv .equiv-proof (y .snd))

fibrewise-is-equiv≃total-is-equiv : ∀[ x ꞉ A ] is-equiv (f x)
                                  ≃ is-equiv (total f)
fibrewise-is-equiv≃total-is-equiv = prop-extₑ!
  fibrewise-is-equiv→total-is-equiv
  total-is-equiv→fibrewise-is-equiv
