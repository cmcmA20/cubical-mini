{-# OPTIONS --safe #-}
module Data.Dec.Sigma where

open import Foundations.Prelude

open import Data.Bool.Base as Bool
  hiding (elim ; rec)
open import Data.Empty.Base as ⊥
  hiding (elim ; rec)
open import Data.Maybe.Base as Maybe
  hiding (elim ; rec)
open import Data.Maybe.Correspondences.Unary.Any
open import Data.Maybe.Membership

open import Data.Reflects.Base
open import Data.Reflects.Sigma

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  P : A → Type ℓ′
  m : Maybe A

-- witness of an indexed predicate being (already) decided
infix 2 _becauseᵐ_
record DecΣ {ℓ ℓ′} {A : 𝒰 ℓ} (P : A → 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  constructor _becauseᵐ_
  field
    doesm  : Maybe A
    proofm : ReflectsΣ P doesm
open DecΣ public

pattern yesm x p = (just x) becauseᵐ ofʲ _ p
pattern nom ¬p   = nothing becauseᵐ ofⁿ ¬p

elim : {C : DecΣ P → 𝒰 ℓ″}
     → ((x : A) → ( p : P x) → C (yesm x p))
     → ((¬p : ∀ x → ¬ P x)   → C (nom ¬p))
     → (d : DecΣ P) → C d
elim y n (yesm x p) = y x p
elim y n (nom np)   = n np

rec : {Q : 𝒰 ℓ″} → ((x : A) → P x → Q) → ((∀ x → ¬ P x) → Q) → DecΣ P → Q
rec {Q} = elim {C = λ _ → Q}

⌊_⌋m : {A : 𝒰 ℓ} {P : A → 𝒰 ℓ′}
    → DecΣ {A = A} P → Maybe A
⌊_⌋m = doesm

decΣ-∈ : (m : Maybe A) → DecΣ (_∈ₘ m)
decΣ-∈ m .doesm  = m
decΣ-∈ m .proofm = reflectsΣ-∈
