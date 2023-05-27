{-# OPTIONS --safe #-}
module Structures.Negation where

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
  n : HLevel

infix 0 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

-- negation is quite a trivial structure
-- btw such "structures" are called _properties_
¬-is-prop : is-prop (¬ A)
¬-is-prop f _ = fun-ext λ x → ⊥.rec (f x)

instance
  H-Level-¬ : H-Level (suc n) (¬ A)
  H-Level-¬ = prop-instance ¬-is-prop

¬-extₑ : ¬ A → ¬ B → A ≃ B
¬-extₑ ¬a ¬b = iso→equiv 𝔯
  where
  𝔯 : _ ≅ _
  𝔯 .fst              a = ⊥.rec (¬a a)
  𝔯 .snd .is-iso.inv  b = ⊥.rec (¬b b)
  𝔯 .snd .is-iso.rinv b = ⊥.rec (¬b b)
  𝔯 .snd .is-iso.linv a = ⊥.rec (¬a a)

Negation-str : Structure {ℓ′} ℓ″ ¬_
Negation-str .is-hom _ _ _ = Lift _ ⊤

@0 negation-str-is-univalent : is-univalent {ℓ} (Negation-str {ℓ′})
negation-str-is-univalent _ = iso→equiv 𝔯
  where
  𝔯 : Iso _ _
  𝔯 .fst _ = to-pathP (¬-is-prop _ _)
  𝔯 .snd .is-iso.inv _ = _
  𝔯 .snd .is-iso.rinv = pathP-is-of-hlevel 1 ¬-is-prop _
  𝔯 .snd .is-iso.linv (lift tt) = refl

negation-action : Equiv-action S → Equiv-action {ℓ′} (λ X → ¬ (S X))
negation-action acts eqv .fst ¬sx sy = ¬sx $ (acts eqv ₑ⁻¹) .fst sy
negation-action acts eqv .snd .equiv-proof ¬sy .fst .fst sx = ¬sy (acts eqv .fst sx)
negation-action acts eqv .snd .equiv-proof ¬sy .fst .snd = fun-ext λ sy → ⊥.rec (¬sy sy)
negation-action acts eqv .snd .equiv-proof ¬sy .snd _ = prop!

@0 negation-action-is-transport : {α : Equiv-action S}
                                → is-transport-str (negation-action α)
negation-action-is-transport _ _ = prop!
