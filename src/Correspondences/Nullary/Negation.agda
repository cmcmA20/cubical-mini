{-# OPTIONS --safe #-}
module Correspondences.Nullary.Negation where

open import Foundations.Base
open import Foundations.Equiv

import Data.Empty.Base as ⊥
open ⊥ public
  using (⊥)

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

infix 0 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

-- negation is quite a trivial structure
-- btw such "structures" are called _properties_
¬-is-prop : is-prop (¬ A)
¬-is-prop f _ = fun-ext λ x → ⊥.rec (f x)

¬-extₑ : ¬ A → ¬ B → A ≃ B
¬-extₑ ¬a ¬b = iso→equiv 𝔯
  where
  𝔯 : _ ≅ _
  𝔯 .fst              a = ⊥.rec (¬a a)
  𝔯 .snd .is-iso.inv  b = ⊥.rec (¬b b)
  𝔯 .snd .is-iso.rinv b = ⊥.rec (¬b b)
  𝔯 .snd .is-iso.linv a = ⊥.rec (¬a a)
