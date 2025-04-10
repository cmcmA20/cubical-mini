{-# OPTIONS --safe #-}
module Data.Dec.Sigma where

open import Foundations.Prelude

open import Data.Bool.Base as Bool
  using (Bool; false; true; not; if_then_else_; is-true; So; oh; Underlying-Bool)
open import Data.Empty.Base as ⊥
  using ()
open import Data.Maybe.Base as Maybe
  using (Maybe; just; nothing)
open import Data.Reflects.Sigma as Reflects
--  using (Reflects⁰; ofⁿ; ofʸ; Reflectance-Underlying)
  public

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  P : A → Type ℓ′
  m : Maybe A

-- witness of a predicate being (already) decided
infix 2 _becauseᵐ_
record DecΣ {ℓ ℓ′} {A : 𝒰 ℓ} (P : A → 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  constructor _becauseᵐ_
  field
    doesm  : Maybe A
    proofm : ReflectsΣ P doesm
open DecΣ public

pattern yesm x p = (just x) becauseᵐ ofʲ _ p
pattern nom ¬p   = nothing becauseᵐ ofⁿ ¬p

elim : {C : DecΣ P → Type ℓ″}
     → ((x : A) → ( p : P x) → C (yesm x p))
     → ((¬p : ∀ x → ¬ P x)   → C (nom ¬p))
     → (d : DecΣ P) → C d
elim y n (yesm x p) = y x p
elim y n (nom np)   = n np

⌊_⌋m : {A : 𝒰 ℓ} {P : A → 𝒰 ℓ′}
    → DecΣ {A = A} P → Maybe A
⌊_⌋m = doesm
