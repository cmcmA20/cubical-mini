{-# OPTIONS --safe #-}
module Foundations.Equiv.Fibrewise where

open import Foundations.Base
open import Foundations.Equiv.Base
open import Foundations.Equiv.Properties
open import Foundations.HLevel
open import Foundations.Isomorphism
open import Foundations.Sigma.Properties

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  P : A → Type ℓ′
  Q : A → Type ℓ″

total : {A : Type ℓ} {P : A → Type ℓ′} {Q : A → Type ℓ″}
      → Π[ x ꞉ A ] (P x → Q x)
      → Σ A P → Σ A Q
total f (x , y) = x , f x y

total-fibres-equiv : {A : Type ℓ} {P : A → Type ℓ′} {Q : A → Type ℓ″}
                     {x : A} {v : Q x}
                     {f : Π[ x ꞉ A ] (P x → Q x)}
                   → fibre (f x)          v
                   ≃ fibre (total f) (x , v)
total-fibres-equiv {A} {Q} {f} = ≅→≃ $ to , iso from ri li where
  to : {x : A} {v : Q x} → fibre (f x) v → fibre (total f) (x , v)
  to (v′ , p) = (_ , v′) , λ i → _ , p i

  from : {x : A} {v : Q x} → fibre (total f) (x , v) → fibre (f x) v
  from ((x , v) , p) = transport (λ i → fibre (f (p i .fst)) (p i .snd)) (v , refl)

  opaque
    unfolding singletonₚ-is-prop
    ri : {x : A} {v : Q x}
       → from {x = x} {v = v} is-right-inverse-of to
    ri ((x , v) , p) =
      Jₚ (λ { _ p → to (from ((x , v) , p)) ＝ ((x , v) , p) })
         (ap to (Jₚ-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl)))
         p

    li : {x : A} {v : Q x}
       → from {x = x} {v = v} is-left-inverse-of to
    li (v , p) =
      Jₚ (λ { _ p → from (to (v , p)) ＝ (v , p) })
         (Jₚ-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl))
         p

total-is-equiv→fibrewise-is-equiv : {f : Π[ x ꞉ A ] (P x → Q x)}
                                  → is-equiv (total f)
                                  → ∀[ x ꞉ A ] is-equiv (f x)
total-is-equiv→fibrewise-is-equiv eqv {x} .equiv-proof y = is-equiv→is-of-hlevel 0
  from (inverse .snd) (eqv .equiv-proof (x , y))
    where open Equiv total-fibres-equiv

fibrewise-is-equiv→total-is-equiv : {f : Π[ x ꞉ A ] (P x → Q x)}
                                  → ∀[ x ꞉ A ] is-equiv (f x)
                                  → is-equiv (total f)
fibrewise-is-equiv→total-is-equiv always-eqv .equiv-proof y = is-equiv→is-of-hlevel 0
  (total-fibres-equiv .fst) (total-fibres-equiv .snd)
  (always-eqv .equiv-proof (y .snd))

fibrewise-is-equiv≃total-is-equiv : {f : Π[ x ꞉ A ] (P x → Q x)}
                                  → ∀[ x ꞉ A ] is-equiv (f x)
                                  ≃ is-equiv (total f)
fibrewise-is-equiv≃total-is-equiv = prop-extₑ!
  fibrewise-is-equiv→total-is-equiv
  total-is-equiv→fibrewise-is-equiv


-- displayed equivalences
module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} where

  _≃[_]_ : ∀{ℓp ℓq} (P : A → Type ℓp) (e : A ≃ B) (Q : B → Type ℓq) → Type _
  P ≃[ e ] Q = (a : A) (b : B) → e .fst a ＝ b → P a ≃ Q b

  module _ {ℓp ℓq} {P : A → Type ℓp} {Q : B → Type ℓq} (e : A ≃ B) where
    private module e = Equiv e

    over-left→over : Π[ a ꞉ A ] (P a ≃ Q (e.to a)) → P ≃[ e ] Q
    over-left→over e′ a _ p = e′ a ∙ line→≃ (λ i → Q (p i))

    over-right→over : Π[ b ꞉ B ] (P (e.from b) ≃ Q b) → P ≃[ e ] Q
    over-right→over e′ _ b p = line→≃ (λ i → P (e.adjunct-l p i)) ∙ e′ b

    prop-over-ext
      : (∀ {a} → is-prop (P a))
      → (∀ {b} → is-prop (Q b))
      → Π[ a ꞉ A ] (P a → Q (e.to a))
      → Π[ b ꞉ B ] (Q b → P (e.from b))
      → P ≃[ e ] Q
    prop-over-ext P-prop Q-prop P→Q Q→P a b p = prop-extₑ P-prop Q-prop
      (subst Q p ∘ P→Q a)
      (subst P (e.adjunct-l p ⁻¹) ∘ Q→P b)

    over→total : P ≃[ e ] Q → Σ A P ≃ Σ B Q
    over→total e′ = Σ-ap e λ a → e′ a (e.to a) refl

    prop-over-ext!
      : ⦃ ∀ {a} → H-Level 1 (P a) ⦄
      → ⦃ ∀ {b} → H-Level 1 (Q b) ⦄
      → Π[ a ꞉ A ] (P a → Q (e.to a))
      → Π[ b ꞉ B ] (Q b → P (e.from b))
      → P ≃[ e ] Q
    prop-over-ext! = prop-over-ext (hlevel 1) (hlevel 1)
