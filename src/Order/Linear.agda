{-# OPTIONS --safe #-}
module Order.Linear where

open import Foundations.Base

open import Meta.Record
open import Meta.Search.HLevel

open import Structures.IdentitySystem

open import Data.Empty.Base
open import Data.Sum.Base

open import Truncation.Propositional as ∥-∥₁

-- move to `Meta.Ord`
-- data Tri {ℓ ℓ′} {A : Type ℓ} (_<_ : A → A → Type ℓ′) (x y : A) : Type (ℓ ⊔ ℓ′) where
--   lt : (  x < y) × (¬ x ＝ y) × (¬ y < x) → Tri _<_ x y
--   eq : (¬ x < y) × (  x ＝ y) × (¬ y < x) → Tri _<_ x y
--   gt : (¬ x < y) × (¬ x ＝ y) × (  y < x) → Tri _<_ x y
-- open import Data.Dec.Base
-- wrong : ∀ {ℓ ℓ′} {A : Type ℓ} {_≤_ : A → A → Type ℓ′} (≤-to : is-linear-order _≤_) {x y} → Dec (x ≤ y)
-- wrong ≤-to {x} {y} with is-linear-order.≤-total ≤-to {x} {y}
-- ... | inl x≤y = yes x≤y
-- ... | inr x₁ = no {!!}

record is-linear-order {ℓ ℓ′} {A : Type ℓ}
          (_<_ : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    instance <-thin : ∀ {x y} → is-prop (x < y)
    <-asym  : ∀ {x y} → x < y → ¬ y < x
    <-cmp   : ∀ {x y z} → x < z → x < y ⊎₁ y < z
    <-conn  : ∀ {x y} → ¬ x < y → ¬ y < x → x ＝ y

  <-irr : ∀ {x} → ¬ x < x
  <-irr p = <-asym p p

  <-trans : ∀ {x y z} → x < y → y < z → x < z
  <-trans p = ∥-∥₁.proj! ∘ ∥-∥₁.map
    [ (λ s → absurd (<-asym p s)) , id ]ᵤ ∘ <-cmp

  instance
    has-is-set : is-set A
    has-is-set = identity-system→is-of-hlevel 1
      {r = λ _ → [ <-irr , <-irr ]ᵤ}
      (set-identity-system hlevel! λ p → <-conn (p ∘ inl) (p ∘ inr))
      hlevel!


private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  R : A → A → Type ℓ′

is-linear-order-is-of-hlevel : ∀ n → is-of-hlevel (suc n) (is-linear-order R)
is-linear-order-is-of-hlevel n = is-of-hlevel-+-left 1 _ is-linear-order-is-prop where
  unquoteDecl eqv = declare-record-iso eqv (quote is-linear-order)
  is-linear-order-is-prop : is-prop (is-linear-order R)
  is-linear-order-is-prop = is-prop-η λ x y →
    let open is-linear-order x in is-prop-β (iso→is-of-hlevel 1 eqv hlevel!) x y

instance
  decomp-hlevel-lo
    : goal-decomposition (quote is-of-hlevel) (is-linear-order R)
  decomp-hlevel-lo = decomp (quote is-linear-order-is-of-hlevel) (`level-minus 1 ∷ [])


record Loset-on {ℓ} ℓ′ (A : Type ℓ) : Type (ℓ ⊔ ℓsuc ℓ′) where
  no-eta-equality
  field
    _<_          : A → A → Type ℓ′
    has-is-loset : is-linear-order _<_
  open is-linear-order has-is-loset public


-- private module Example where

--   open import Data.Nat
--   open import Data.Nat.Order.Inductive

--   what : is-linear-order _<_
--   what .is-linear-order.<-thin = ≤-is-prop
--   what .is-linear-order.<-asym p q = ¬sucn≤n (≤-trans (≤-suc-r p) q)
--   what .is-linear-order.<-cmp {x} {y} {z} p with ≤-split x y
--   ... | inl u = ∣ inl u ∣₁
--   ... | inr (inl v) = ∣ inr $ ≤-trans (≤-suc-r v) p ∣₁
--   ... | inr (inr w) = ∣ inr $ subst (_≤ z) (ap suc w) p ∣₁
--   what .is-linear-order.<-conn {x} {y} p q with ≤-split x y
--   ... | inl u = absurd (p u)
--   ... | inr (inl v) = absurd (q v)
--   ... | inr (inr w) = w

--   kek : Loset-on 0ℓ ℕ
--   kek .Loset-on._<_ = _<_
--   kek .Loset-on.has-is-loset = what
