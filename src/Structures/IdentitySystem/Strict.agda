{-# OPTIONS --safe #-}
module Structures.IdentitySystem.Strict where

open import Foundations.Base

open import Meta.Marker
open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ′
  R : A → A → Type ℓ′
  r : ∀ a → R a a

opaque
  unfolding is-of-hlevel
  set-identity-is-prop
    : ∀ {r : (a : A) → R a a} {a b : A}
    → is-identity-system R r
    → is-set A
    → is-prop (R a b)
  set-identity-is-prop {R} {a} {b} ids set =
    is-of-hlevel-≃ 1 (identity-system-gives-path ids) (set a b)

  K
    : {r : (a : A) → R a a} {a : A}
    → is-identity-system R r
    → is-set A
    → (P : R a a → Type ℓ″) → P (r a) → ∀ s → P s
  K {r} {a} ids set P pr s =
    transport (λ i → P (set-identity-is-prop ids set (r a) s i)) pr

  K-refl
    : {r : ∀ a → R a a} {a : A}
    → (ids : is-identity-system R r)
    → (set : is-set A)
    → (P : R a a → Type ℓ″)
    → (p : P (r a))
    → K ids set P p (r a) ＝ p
  K-refl {R} {r} {a} ids set P p =
    transport (λ i → P (set-identity-is-prop ids set (r a) (r a) i)) p ＝⟨⟩
    subst P   ⌜ set-identity-is-prop ids set (r a) (r a) ⌝           p ＝⟨ ap! lemma ⟩
    transport (λ _ → P (r a))                                        p ＝⟨ transport-refl p ⟩
    p                                                                  ∎
    where
      lemma : set-identity-is-prop ids set (r a) (r a) ＝ refl
      lemma = is-prop→is-set (set-identity-is-prop ids set) (r a) (r a) _ _
