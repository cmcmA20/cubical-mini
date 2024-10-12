{-# OPTIONS --safe #-}
open import Order.Base
open import Order.Diagram.Lub

module Order.Diagram.Lub.Reasoning
  {o ℓ} (P : Poset o ℓ) {ℓ′} (hl : Has-lubs-of-size P ℓ′)
  where

open import Algebra.Monoid.Commutative
open import Cat.Prelude

open import Order.Diagram.Bottom
open import Order.Diagram.Join
open Poset P

open import Data.Bool as Bool

lubs : {I : Type ℓ′} (F : I → Ob) → Lub P F
lubs F = hl {F = F}

⋃ : {I : Type ℓ′} (F : I → Ob) → Ob
⋃ F = lubs F .Lub.lub

module lubs {I} {F} = Lub (lubs {I} F)
open lubs renaming
  ( fam≤lub to ⋃-inj
  ; least   to ⋃-universal
  ) public

instance
  Bottom-Poset-Lub : Bottom P
  Bottom-Poset-Lub .Bottom.bot = ⋃ {I = Lift ℓ′ ⊥} λ()
  Bottom-Poset-Lub .Bottom.has-bot _ = ⋃-universal _ λ ()

  Join-Poset-Lub : Has-joins P
  Join-Poset-Lub {x} {y} .Join.lub = ⋃ {I = Lift ℓ′ Bool} (rec! (if_then x else y))
  Join-Poset-Lub .Join.has-join .is-join.l≤join = ⋃-inj (lift true)
  Join-Poset-Lub .Join.has-join .is-join.r≤join = ⋃-inj (lift false)
  Join-Poset-Lub .Join.has-join .is-join.least ub′ p q = ⋃-universal _ (elim! (Bool.elim p q))

open Bottom Bottom-Poset-Lub public
open import Order.Diagram.Join.Reasoning P Join-Poset-Lub public

⋃≤⋃-over
  : {I J : Type ℓ′} {f : I → Ob} {g : J → Ob}
  → (to : I → J)
  → (∀ i → f i ≤ g (to i))
  → ⋃ f ≤ ⋃ g
⋃≤⋃-over to p = ⋃-universal _ λ i → p i ∙ ⋃-inj (to i)

⋃≤⋃
  : {I : Type ℓ′} {f g : I → Ob}
  → (∀ i → f i ≤ g i)
  → ⋃ f ≤ ⋃ g
⋃≤⋃ = ⋃≤⋃-over refl

opaque
  ⋃-twice
    : {I : Type ℓ′} {J : I → Type ℓ′} (F : (i : I) → J i → Ob)
    →  ⋃ (λ i → ⋃ λ j → F i j)
    ＝ ⋃ {I = Σ[ i ꞉ I ] J i} (λ p → F (p .fst) (p .snd))
  ⋃-twice F = ≤-antisym
    (⋃-universal _ λ i → ⋃-universal _ λ j → ⋃-inj (i , j))
    (⋃-universal _ (λ (i , j) → ⋃-inj j ∙ ⋃-inj i))

  ⋃-singleton
    : {I : Type ℓ′} {f : I → Ob}
    → (p : is-contr I)
    → ⋃ f ＝ f (centre p)
  ⋃-singleton {f} p = ≤-antisym
    (⋃-universal _ (λ i → =→≥ (ap f (paths p i))))
    (⋃-inj _)

module @0 _ {I : Type ℓ′} where opaque
  ⋃-ap
    : {I′ : Type ℓ′} {f : I → Ob} {g : I′ → Ob}
    → (e : I ≃ I′)
    → (∀ i → f i ＝ g (e $ i))
    → ⋃ f ＝ ⋃ g
  ⋃-ap e p = ap² (λ _ → ⋃) (ua e) (ua→ p)

  -- raised i for "index", raised f for "family"
  ⋃-apⁱ : {I′ : Type ℓ′} {f : I′ → Ob} (e : I ≃ I′) → ⋃ {I = I} (λ i → f (e # i)) ＝ ⋃ f
  ⋃-apⁱ e = ⋃-ap e (λ _ → refl)

  ⋃-apᶠ : {f g : I → Ob} → (∀ i → f i ＝ g i) → ⋃ f ＝ ⋃ g
  ⋃-apᶠ p = ⋃-ap refl p

∪-distrib-⋃-≤-l
  : {I : Type ℓ′} {x : Ob} {f : I → Ob}
  → ⋃ (λ i → x ∪ f i) ≤ x ∪ ⋃ f
∪-distrib-⋃-≤-l =
  ⋃-universal _ λ i → ∪-universal _ l≤∪ (⋃-inj i ∙ r≤∪)

∪-distrib-inhabited-⋃-l
  : {I : Type ℓ′} {x : Ob} {f : I → Ob}
  → ∥ I ∥₁
  → ⋃ (λ i → x ∪ f i) ＝ x ∪ ⋃ f
∪-distrib-inhabited-⋃-l i =
  ≤-antisym
    ∪-distrib-⋃-≤-l
    (rec! (λ i → ∪-universal _ (l≤∪ ∙ ⋃-inj i) (⋃≤⋃ λ _ → r≤∪)) i)
