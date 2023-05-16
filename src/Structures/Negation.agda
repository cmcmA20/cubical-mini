{-# OPTIONS --safe #-}
module Structures.Negation where

open import Foundations.Base
open import Foundations.HLevel
open import Foundations.Univalence
open import Foundations.Transport
open import Data.Empty.Base as ⊥
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  S : Type ℓ → Type ℓ′

infix 5 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

¬-is-prop : is-prop (¬ A)
¬-is-prop f _ = fun-ext λ x → ⊥.rec (f x)

Negation-str : Structure {ℓ′} ℓ″ ¬_
Negation-str .is-hom _ _ _ = ⊤*

@0 Negation-str-is-univalent : is-univalent {ℓ} (Negation-str {ℓ′})
Negation-str-is-univalent {X = X , ¬x} {Y = Y , ¬y} f = Iso→Equiv 𝔯
  where
  𝔯 : Iso _ _
  𝔯 .fst _ = to-PathP (¬-is-prop _ _)
  𝔯 .snd .is-iso.inv _ = _
  𝔯 .snd .is-iso.rinv = PathP-is-of-hlevel 1 ¬-is-prop _
  𝔯 .snd .is-iso.linv (lift tt) = refl

-- Negation-action : Equiv-action S → Equiv-action {ℓ′} (λ X → ¬ (S X))
-- Negation-action acts eqv = {!!}

-- @0 Negation-action-is-transport : is-transport-str (Negation-action {!!})
-- Negation-action-is-transport f s = {!!}

is-non-empty : Type ℓ → Type ℓ
is-non-empty A = ¬ ¬ A

is-stable : Type ℓ → Type ℓ
is-stable A = is-non-empty A → A

-- TODO move
-- _≠_ : A → A → Type (level-of-type A)
-- x ≠ y = ¬ (x ＝ y)
