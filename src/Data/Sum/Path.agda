{-# OPTIONS --safe #-}
module Data.Sum.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Empty

open import Meta.Reflection.HLevel

open import Structures.Instances.Negation
open import Structures.Instances.IdentitySystem.Base

open import Data.Sum.Base public

private variable
  a b : Level
  A : Type a
  B : Type b
  x : A
  y : B

module path-code where
  Code : A ⊎ B → A ⊎ B → Type (level-of-type A ⊔ level-of-type B)
  Code {B} (inj-l x₁) (inj-l x₂) = Lift (level-of-type B) (x₁ ＝ x₂)
  Code     (inj-l _)  (inj-r _)  = ⊥*
  Code     (inj-r _)  (inj-l _)  = ⊥*
  Code {A} (inj-r y₁) (inj-r y₂) = Lift (level-of-type A) (y₁ ＝ y₂)

  code-refl : (s : A ⊎ B) → Code s s
  code-refl (inj-l x) = lift refl
  code-refl (inj-r y) = lift refl

  ⊎-identity-system : is-identity-system {A = A ⊎ B} Code code-refl
  ⊎-identity-system .to-path {inj-l x₁} {inj-l x₂} c = ap inj-l (lower c)
  ⊎-identity-system .to-path {inj-r y₁} {inj-r y₂} c = ap inj-r (lower c)
  ⊎-identity-system .to-path-over {inj-l x₁} {inj-l x₂} (lift p) i = lift λ j → p (i ∧ j)
  ⊎-identity-system .to-path-over {inj-r y₁} {inj-r y₂} (lift p) i = lift λ j → p (i ∧ j)

  Code-is-of-hlevel : {s₁ s₂ : A ⊎ B} {n : HLevel}
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (2 + n) B
                    → is-of-hlevel (1 + n) (Code s₁ s₂)
  Code-is-of-hlevel {s₁ = inj-l x₁} {inj-l x₂} ahl bhl = Lift-is-of-hlevel _ (ahl x₁ x₂)
  Code-is-of-hlevel {s₁ = inj-l x}  {inj-r y}  ahl bhl = Lift-is-of-hlevel _ hlevel!
  Code-is-of-hlevel {s₁ = inj-r x}  {inj-l y}  ahl bhl = Lift-is-of-hlevel _ hlevel!
  Code-is-of-hlevel {s₁ = inj-r y₁} {inj-r y₂} ahl bhl = Lift-is-of-hlevel _ (bhl y₁ y₂)

open path-code

⊎-is-hlevel : (n : HLevel)
            → is-of-hlevel (2 + n) A
            → is-of-hlevel (2 + n) B
            → is-of-hlevel (2 + n) (A ⊎ B)
⊎-is-hlevel n ahl bhl _ _ =
  is-of-hlevel-≃ (1 + n) (identity-system-gives-path ⊎-identity-system ₑ⁻¹) (Code-is-of-hlevel ahl bhl)

disjoint-⊎-is-prop
  : is-prop A → is-prop B → ¬ A × B
  → is-prop (A ⊎ B)
disjoint-⊎-is-prop Ap Bp notab (inj-l x₁) (inj-l x₂) = ap inj-l (Ap x₁ x₂)
disjoint-⊎-is-prop Ap Bp notab (inj-l x)  (inj-r y)  = absurd (notab (x , y))
disjoint-⊎-is-prop Ap Bp notab (inj-r x)  (inj-l y)  = absurd (notab (y , x))
disjoint-⊎-is-prop Ap Bp notab (inj-r y₁) (inj-r y₂) = ap inj-r (Bp y₁ y₂)


inj-l-inj : {x y : A} → inj-l {B = B} x ＝ inj-l y → x ＝ y
inj-l-inj {A} {x} path = ap f path where
  f : A ⊎ B → A
  f (inj-l a) = a
  f (inj-r _) = x

inj-r-inj : {x y : B} → inj-r {A = A} x ＝ inj-r y → x ＝ y
inj-r-inj {B} {x} path = ap f path where
  f : A ⊎ B → B
  f (inj-l _) = x
  f (inj-r b) = b

⊎-disjoint : ¬ inj-l x ＝ inj-r y
⊎-disjoint p = subst ⊎-discrim p tt
  where
  ⊎-discrim : A ⊎ B → Type
  ⊎-discrim (inj-l _) = ⊤
  ⊎-discrim (inj-r _) = ⊥
