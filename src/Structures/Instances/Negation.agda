{-# OPTIONS --safe #-}
module Structures.Instances.Negation where

open import Foundations.Base
open import Foundations.HLevel
open import Foundations.Sigma
open import Foundations.Univalence

open import Data.Empty.Base public
  using (⊥)
import      Data.Empty as ⊥
open import Data.Unit.Base

open import Meta.Reflection.HLevel

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  S : Type ℓ → Type ℓ′

infix 5 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

-- negation is quite a trivial structure
-- btw such "structures" are called _properties_
¬-is-prop : is-prop (¬ A)
¬-is-prop f _ = fun-ext λ x → ⊥.rec (f x)

¬-extₑ : ¬ A → ¬ B → A ≃ B
¬-extₑ ¬a ¬b = Iso→Equiv 𝔯
  where
  𝔯 : _ ≅ _
  𝔯 .fst              a = ⊥.rec (¬a a)
  𝔯 .snd .is-iso.inv  b = ⊥.rec (¬b b)
  𝔯 .snd .is-iso.rinv b = ⊥.rec (¬b b)
  𝔯 .snd .is-iso.linv a = ⊥.rec (¬a a)

Negation-str : Structure {ℓ′} ℓ″ ¬_
Negation-str .is-hom _ _ _ = ⊤*

@0 Negation-str-is-univalent : is-univalent {ℓ} (Negation-str {ℓ′})
Negation-str-is-univalent _ = Iso→Equiv 𝔯
  where
  𝔯 : Iso _ _
  𝔯 .fst _ = to-PathP (¬-is-prop _ _)
  𝔯 .snd .is-iso.inv _ = _
  𝔯 .snd .is-iso.rinv = PathP-is-of-hlevel 1 ¬-is-prop _
  𝔯 .snd .is-iso.linv (lift tt) = refl

Negation-action : Equiv-action S → Equiv-action {ℓ′} (λ X → ¬ (S X))
Negation-action acts eqv .fst ¬sx sy = ¬sx $ (acts eqv ₑ⁻¹) .fst sy
Negation-action acts eqv .snd .equiv-proof ¬sy .fst .fst sx = ¬sy (acts eqv .fst sx)
Negation-action acts eqv .snd .equiv-proof ¬sy .fst .snd = fun-ext λ sy → ⊥.rec (¬sy sy)
Negation-action acts eqv .snd .equiv-proof ¬sy .snd _ = prop!

@0 Negation-action-is-transport : {α : Equiv-action S}
                                → is-transport-str (Negation-action α)
Negation-action-is-transport _ _ = prop!

-- TODO move out
is-non-empty : Type ℓ → Type ℓ
is-non-empty A = ¬ ¬ A

is-stable : Type ℓ → Type ℓ
is-stable A = is-non-empty A → A

-- TODO move
-- _≠_ : A → A → Type (level-of-type A)
-- x ≠ y = ¬ (x ＝ y)
