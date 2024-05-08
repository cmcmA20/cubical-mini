{-# OPTIONS --safe #-}
module Data.Reflects.Path where

open import Meta.Prelude

open import Meta.Extensionality

open import Data.Bool.Base
open import Data.Empty.Base as ⊥
open import Data.Maybe.Base
open import Data.Reflects.Base
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓᵃ ℓᵇ : Level
  a b : Bool
  A : Type ℓᵃ

ofʸ-inj : ∀ {x y : A} → ofʸ x ＝ ofʸ y → x ＝ y
ofʸ-inj = ap invert-true

ofⁿ-inj : ∀ {x y : ¬ A} → ofⁿ x ＝ ofⁿ y → x ＝ y
ofⁿ-inj _ = prop!

module _ {ℓᵃ ℓ} {A : Type ℓᵃ} ⦃ sa : Extensional A ℓ ⦄ where

  Code-reflects : (x y : Reflects⁰ A a) → Type ℓ
  Code-reflects (ofʸ p) (ofʸ  p′) = sa .Pathᵉ p p′
  Code-reflects (ofⁿ _) (ofⁿ  _)  = Lift _ ⊤

  instance
    Extensional-Reflects : Extensional (Reflects⁰ A a) ℓ
    Extensional-Reflects .Pathᵉ = Code-reflects
    Extensional-Reflects .reflᵉ (ofʸ p) = sa .reflᵉ p
    Extensional-Reflects .reflᵉ (ofⁿ _) = _
    Extensional-Reflects .idsᵉ .to-path {ofʸ  p} {ofʸ  p′}  = ap ofʸ ∘ sa .idsᵉ .to-path
    Extensional-Reflects .idsᵉ .to-path {ofⁿ _}  {ofⁿ _}  _ = ap ofⁿ prop!
    Extensional-Reflects .idsᵉ .to-path-over {ofʸ p} {ofʸ p′}   = sa .idsᵉ .to-path-over
    Extensional-Reflects .idsᵉ .to-path-over {ofⁿ _} {ofⁿ _}  _ = prop!

code-reflects-is-of-hlevel : {x y : Reflects⁰ A a} {n : HLevel}
                           → is-of-hlevel (suc n) A
                           → is-of-hlevel n (Code-reflects x y)
code-reflects-is-of-hlevel {x = ofʸ p} {ofʸ p′} hl = path-is-of-hlevel _ hl p p′
code-reflects-is-of-hlevel {x = ofⁿ _} {ofⁿ _}  _  = hlevel _

reflects-true-is-contr : is-contr A → is-contr (Reflects⁰ A true)
reflects-true-is-contr (p , paths) = ofʸ p , λ where
  (ofʸ q) → ap ofʸ (paths q)

opaque
  reflects-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) A → is-of-hlevel (suc n) (Reflects⁰ A a)
  reflects-is-of-hlevel 0 hl (ofʸ p) (ofʸ p′) = ap ofʸ (hl p p′)
  reflects-is-of-hlevel 0 _  (ofⁿ _) (ofⁿ _)  = ap ofⁿ prop!
  reflects-is-of-hlevel (suc n) hl = identity-system→is-of-hlevel (suc n) (Extensional-Reflects .idsᵉ)
    λ x _ → code-reflects-is-of-hlevel {x = x} hl

instance opaque
  H-Level-Reflects : ∀ {n} → ⦃ H-Level (suc n) A ⦄ → H-Level (suc n) (Reflects⁰ A a)
  H-Level-Reflects .H-Level.has-of-hlevel = reflects-is-of-hlevel _ (hlevel _)
