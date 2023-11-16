{-# OPTIONS --safe #-}
module Truncation.Propositional.Base where

open import Foundations.Base

open import Meta.Search.HLevel
open import Meta.Variadic

open import Data.Sum.Base
  using (_⊎_)

data ∥_∥₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₁    : A → ∥ A ∥₁
  squash₁ : (x y : ∥ A ∥₁) → x ＝ y

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

rec : is-prop B → (A → B) → ∥ A ∥₁ → B
rec B-prop f ∣ x ∣₁ = f x
rec B-prop f (squash₁ x y i) = is-prop-β B-prop (rec B-prop f x) (rec B-prop f y) i

∥-∥₁-is-prop : is-prop ∥ A ∥₁
∥-∥₁-is-prop = is-prop-η squash₁

∥-∥₁-is-of-hlevel : ∀ n → is-of-hlevel (suc n) ∥ A ∥₁
∥-∥₁-is-of-hlevel n = is-prop→is-of-hlevel-suc ∥-∥₁-is-prop

instance
  H-Level-∥-∥₁ : ∀ {n} → H-Level (suc n) ∥ A ∥₁
  H-Level-∥-∥₁ = hlevel-prop-instance ∥-∥₁-is-prop

  decomp-hlevel-∥-∥₁ : goal-decomposition (quote is-of-hlevel) ∥ A ∥₁
  decomp-hlevel-∥-∥₁ = decomp (quote ∥-∥₁-is-of-hlevel ) (`level-minus 1 ∷ [])

map : (A → B) → (∥ A ∥₁ → ∥ B ∥₁)
map f = rec (hlevel 1) (∣_∣₁ ∘ f)

proj : (A-prop : is-prop A) → ∥ A ∥₁ → A
proj A-prop = rec A-prop id

elim : {P : ∥ A ∥₁ → Type ℓ′}
     → Π[ x ꞉ ∥ A ∥₁ ] is-prop (P x)
     → Π[ x ꞉   A    ] P ∣ x ∣₁
     → Π[ x ꞉ ∥ A ∥₁ ] P   x
elim P-prop incc ∣ x ∣₁ = incc x
elim P-prop incc (squash₁ x y i) =
  is-prop→pathP (λ j → P-prop (squash₁ x y j)) (elim P-prop incc x)
                                               (elim P-prop incc y)
                                               i


-- Mere existence

∃ : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃ A B = ∥ Σ[ a ꞉ A ] B a ∥₁

infixr 6 ∃-syntax

∃-syntax : (A : Type ℓ) (B : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ꞉ A ] B

Existential₁ⁿ
  : {arity : ℕ} {ls : Levels arity} {As : Types arity ls}
    {ℓ : Level} {U : Type ℓ} ⦃ u : Underlying U ⦄
  → SCorr arity As U → Type (u .ℓ-underlying ⊔ ℓsup arity ls)
Existential₁ⁿ {0}                         P = ∥ ⌞ P ⌟⁰ ∥₁
Existential₁ⁿ {1}           {As = A}      P = ∥ Σ[ a ꞉ A ] ⌞ P a ⌟⁰ ∥₁
Existential₁ⁿ {suc (suc _)} {As = A , As} P = ∥ Σ[ a ꞉ A ] Existentialⁿ (P a) ∥₁

macro ∃[_] = quantifier-macro (quote Existential₁ⁿ)


-- Mere disjunction
infixr 7 _⊎₁_
_⊎₁_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ ℓ′)
A ⊎₁ B = ∥ A ⊎ B ∥₁


Im : (A → B) → Type _
Im {A} {B} f = Σ[ b ꞉ B ] ∃[ a ꞉ A ] (f a ＝ b)
