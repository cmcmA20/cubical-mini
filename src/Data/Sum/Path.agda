{-# OPTIONS --safe #-}
module Data.Sum.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

open import Data.Empty.Base

open import Data.Sum.Base public

private variable
  a b : Level
  A : Type a
  B : Type b
  x : A
  y : B

module ⊎-path-code where

  Code : A ⊎ B → A ⊎ B → Type (level-of-type A ⊔ level-of-type B)
  Code {B} (inl x₁) (inl x₂) = Lift (level-of-type B) (x₁ ＝ x₂)
  Code     (inl _)  (inr _)  = Lift _ ⊥
  Code     (inr _)  (inl _)  = Lift _ ⊥
  Code {A} (inr y₁) (inr y₂) = Lift (level-of-type A) (y₁ ＝ y₂)

  code-refl : (s : A ⊎ B) → Code s s
  code-refl (inl x) = lift refl
  code-refl (inr y) = lift refl

  ⊎-identity-system : is-identity-system {A = A ⊎ B} Code code-refl
  ⊎-identity-system .to-path {inl x₁} {inl x₂} c = ap inl (lower c)
  ⊎-identity-system .to-path {inr y₁} {inr y₂} c = ap inr (lower c)
  ⊎-identity-system .to-path-over {inl x₁} {inl x₂} (lift p) i = lift λ j → p (i ∧ j)
  ⊎-identity-system .to-path-over {inr y₁} {inr y₂} (lift p) i = lift λ j → p (i ∧ j)

  opaque
    unfolding is-of-hlevel
    code-is-of-hlevel : {s₁ s₂ : A ⊎ B} {n : HLevel}
                      → is-of-hlevel (2 + n) A
                      → is-of-hlevel (2 + n) B
                      → is-of-hlevel (1 + n) (Code s₁ s₂)
    code-is-of-hlevel {s₁ = inl x₁} {inl x₂} ahl bhl = Lift-is-of-hlevel _ (ahl x₁ x₂)
    code-is-of-hlevel {s₁ = inl x}  {inr y}  ahl bhl = hlevel!
    code-is-of-hlevel {s₁ = inr x}  {inl y}  ahl bhl = hlevel!
    code-is-of-hlevel {s₁ = inr y₁} {inr y₂} ahl bhl = Lift-is-of-hlevel _ (bhl y₁ y₂)

open ⊎-path-code

opaque
  unfolding is-of-hlevel
  ⊎-is-of-hlevel : (n : HLevel)
                 → is-of-hlevel (2 + n) A
                 → is-of-hlevel (2 + n) B
                 → is-of-hlevel (2 + n) (A ⊎ B)
  ⊎-is-of-hlevel n ahl bhl _ _ =
    is-of-hlevel-≃ (1 + n) (identity-system-gives-path ⊎-identity-system ₑ⁻¹) (code-is-of-hlevel ahl bhl)

  disjoint-⊎-is-prop
    : is-prop A → is-prop B → ¬ A × B
    → is-prop (A ⊎ B)
  disjoint-⊎-is-prop Ap Bp notab (inl x₁) (inl x₂) = ap inl (Ap x₁ x₂)
  disjoint-⊎-is-prop Ap Bp notab (inl x)  (inr y)  = absurd (notab (x , y))
  disjoint-⊎-is-prop Ap Bp notab (inr x)  (inl y)  = absurd (notab (y , x))
  disjoint-⊎-is-prop Ap Bp notab (inr y₁) (inr y₂) = ap inr (Bp y₁ y₂)

contr-⊎-is-set
  : is-contr A → is-contr B
  → is-set (A ⊎ B)
contr-⊎-is-set A-contr B-contr = identity-system→hlevel 1 ⊎-identity-system go where opaque
  unfolding is-of-hlevel
  go : _
  go (inl x)  (inr y)  = Lift-is-of-hlevel 1 ⊥-is-prop
  go (inr y)  (inl x)  = Lift-is-of-hlevel 1 ⊥-is-prop
  go (inl x₁) (inl x₂) = Lift-is-of-hlevel 1 $ is-contr→is-set A-contr _ _
  go (inr y₁) (inr y₂) = Lift-is-of-hlevel 1 $ is-contr→is-set B-contr _ _

inl-inj : {x y : A} → inl {B = B} x ＝ inl y → x ＝ y
inl-inj {A} {x} path = ap f path where
  f : A ⊎ B → A
  f (inl a) = a
  f (inr _) = x

inr-inj : {x y : B} → inr {A = A} x ＝ inr y → x ＝ y
inr-inj {B} {x} path = ap f path where
  f : A ⊎ B → B
  f (inl _) = x
  f (inr b) = b

⊎-disjoint : ¬ inl x ＝ inr y
⊎-disjoint p = subst ⊎-discrim p tt
  where
  ⊎-discrim : A ⊎ B → Type
  ⊎-discrim (inl _) = ⊤
  ⊎-discrim (inr _) = ⊥
