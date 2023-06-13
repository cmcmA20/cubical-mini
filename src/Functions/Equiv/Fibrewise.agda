{-# OPTIONS --safe #-}
module Functions.Equiv.Fibrewise where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.HLevel
open import Foundations.Isomorphism

private variable
  ℓ ℓ′ : Level
  A B : Type ℓ
  P Q : A → Type ℓ′
  f : Π[ x ꞉ A ] (P x → Q x)
  x : A
  v : Q x

total : (Π[ x ꞉ A ] (P x → Q x))
      → Σ A P → Σ A Q
total f (x , y) = x , f x y

total-fibres : {f : Π[ a ꞉ A ] (P a → Q a)}
               {x : A} {v : Q x}
             → fibre (f x)          v
             ≅ fibre (total f) (x , v)
total-fibres {A} {Q} {f} = the-iso where
  open is-iso

  to : {x : A} {v : Q x} → fibre (f x) v → fibre (total f) (x , v)
  to (v′ , p) = (_ , v′) , λ i → _ , p i

  from : {x : A} {v : Q x} → fibre (total f) (x , v) → fibre (f x) v
  from ((x , v) , p) = transport (λ i → fibre (f (p i .fst)) (p i .snd)) (v , refl)

  the-iso : {x : A} {v : Q x} → fibre (f x) v ≅ fibre (total f) (x , v)
  the-iso .fst = to
  the-iso .snd .is-iso.inv = from
  the-iso .snd .is-iso.rinv ((x , v) , p) =
    J (λ { _ p → to (from ((x , v) , p)) ＝ ((x , v) , p) })
      (ap to (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl)))
      p
  the-iso .snd .is-iso.linv (v , p) =
    J (λ { _ p → from (to (v , p)) ＝ (v , p) })
      (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl))
      p

total→is-equiv : {f : Π[ x ꞉ A ] (P x → Q x)}
               → is-equiv (total f)
               → {x : A} → is-equiv (f x)
total→is-equiv eqv {x} .equiv-proof y =
  is-iso→is-of-hlevel 0 (total-fibres .snd .is-iso.inv)
                        (is-iso-inv (total-fibres .snd))
                        (eqv .equiv-proof (x , y))

is-equiv→total : {f : Π[ x ꞉ A ] (P x → Q x)}
               → ({x : A} → is-equiv (f x))
               → is-equiv (total f)
is-equiv→total always-eqv .equiv-proof y =
  is-iso→is-of-hlevel 0
    (total-fibres .fst)
    (total-fibres .snd)
    (always-eqv .equiv-proof (y .snd))
