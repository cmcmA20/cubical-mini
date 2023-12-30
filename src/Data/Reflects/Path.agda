{-# OPTIONS --safe #-}
module Data.Reflects.Path where

open import Foundations.Base
open import Foundations.Equiv
open import Foundations.HLevel

open import Meta.Search.HLevel

open import Structures.IdentitySystem.Base

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Maybe.Base

open import Data.Reflects.Base

private variable
  ℓ ℓ′ : Level
  a b : Bool
  P : Type ℓ
  Q : Type ℓ′

Code : (x y : Reflects⁰ P a) → Type (level-of-type P)
Code (ofʸ p) (ofʸ p′) = p ＝ p′
Code (ofⁿ _) (ofⁿ _)  = Lift _ ⊤

code-refl : (x : Reflects⁰ P a) → Code x x
code-refl (ofʸ _) = refl
code-refl (ofⁿ _) = lift tt

identity-system : is-identity-system {A = Reflects⁰ P a} Code code-refl
identity-system .to-path {ofʸ _}  {ofʸ _} = ap ofʸ
identity-system .to-path {ofⁿ ¬p} {ofⁿ ¬p′} _ = ap ofⁿ (fun-ext (λ p → ⊥.rec (¬p p)))
identity-system .to-path-over {ofʸ p} {ofʸ p′} c i j = c (i ∧ j)
identity-system .to-path-over {ofⁿ ¬p} {ofⁿ ¬p′} _ = refl

opaque
  unfolding is-of-hlevel
  code-is-of-hlevel : {x y : Reflects⁰ P a} {n : HLevel}
                    → is-of-hlevel (suc n) P
                    → is-of-hlevel n (Code x y)
  code-is-of-hlevel {x = ofʸ p} {ofʸ p′} hl = path-is-of-hlevel′ _ hl p p′
  code-is-of-hlevel {x = ofⁿ _} {ofⁿ _}  _  = hlevel!

  reflects-true-is-contr : is-contr P → is-contr (Reflects⁰ P true)
  reflects-true-is-contr (p , paths) = ofʸ p , λ where
    (ofʸ q) → ap ofʸ (paths q)

  reflects-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) P → is-of-hlevel (suc n) (Reflects⁰ P a)
  reflects-is-of-hlevel 0 hl (ofʸ p) (ofʸ p′) = ap ofʸ (hl p p′)
  reflects-is-of-hlevel 0 _  (ofⁿ _) (ofⁿ _)  = ap ofⁿ prop!
  reflects-is-of-hlevel (suc n) hl _ _ = is-of-hlevel-≃ (1 + n)
    (identity-system-gives-path identity-system ₑ⁻¹) $ code-is-of-hlevel hl

ofʸ-inj : ∀ {x y : P} → ofʸ x ＝ ofʸ y → x ＝ y
ofʸ-inj = ap invert-true

ofⁿ-inj : ∀ {x y : ¬ P} → ofⁿ x ＝ ofⁿ y → x ＝ y
ofⁿ-inj _ = prop!

instance
  decomp-hlevel-reflects
    : goal-decomposition (quote is-of-hlevel) (Reflects⁰ P a)
  decomp-hlevel-reflects = decomp (quote reflects-is-of-hlevel)
    [ `level-minus 1 , `search (quote is-of-hlevel) ]
