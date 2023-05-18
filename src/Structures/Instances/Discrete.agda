{-# OPTIONS --safe #-}
module Structures.Instances.Discrete where

open import Foundations.Base

open import Data.Dec.Base public

open import Structures.Path public

private variable
  ℓ : Level

-- Dec-is-prop : is-prop (Dec P)
-- Dec-is-prop (no ¬p) (no ¬p′) = ap no (fun-ext λ p → ⊥.rec (¬p p))
-- Dec-is-prop (no ¬p) (yes p ) = ⊥.rec (¬p p)
-- Dec-is-prop (yes p) (no ¬p ) = ⊥.rec (¬p p)
-- Dec-is-prop (yes p) (yes p′) = ap yes {!!}

Discrete : Type ℓ → Type ℓ
Discrete A = Dec on-paths-of A

-- FIXME not so useful without Hedberg's lemma
-- is-set→Discrete-is-prop : is-set A → is-prop (Discrete A)
-- is-set→Discrete-is-prop A-set d₁ d₂ i x y with d₁ x y | d₂ x y
-- ... | false because p | false because q = false because is-prop→reflects-is-prop (A-set _ _) p q i
-- ... | false because p | true  because q = let t = reflects-ext p q in {!!}
-- ... | true because  p | false because q = {!!}
-- ... | true because  p | true  because q = true because is-prop→reflects-is-prop (A-set _ _) p q i
