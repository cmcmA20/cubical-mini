{-# OPTIONS --safe #-}
module Correspondences.Nullary.Decidable where

open import Foundations.Base
open import Foundations.HLevel

open import Correspondences.Nullary.Separated

open import Data.Bool.Base
import Data.Dec.Base as Dec
open import Data.Dec.Path
open import Data.Empty.Base

open import Functions.Embedding

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′
  n : HLevel

opaque
  is-decidable-at-hlevel : HLevel → Type ℓ → Type ℓ
  is-decidable-at-hlevel 0       = Dec
  is-decidable-at-hlevel (suc n) = is-decidable-at-hlevel n on-paths-of_

-- TODO can we drop this?
Decision : Type ℓ → Type ℓ
Decision = is-decidable-at-hlevel 0

is-discrete : Type ℓ → Type ℓ
is-discrete = is-decidable-at-hlevel 1

opaque
  unfolding is-decidable-at-hlevel

  decision-β : Decision A → Dec A
  decision-β = id

  decision-η : Dec A → Decision A
  decision-η = id

  is-discrete-β : is-discrete A → Π[ x ꞉ A ] Π[ y ꞉ A ] Dec (x ＝ y)
  is-discrete-β = id

  is-discrete-η : Π[ x ꞉ A ] Π[ y ꞉ A ] Dec (x ＝ y) → is-discrete A
  is-discrete-η = id

  opaque
    unfolding is-separated-at-hlevel
    is-decidable-at-hlevel→is-separated-at-hlevel
      : (n : HLevel) → is-decidable-at-hlevel n A → is-separated-at-hlevel n A
    is-decidable-at-hlevel→is-separated-at-hlevel 0 = dec→¬¬-stable
    is-decidable-at-hlevel→is-separated-at-hlevel (suc n) di x y =
     is-decidable-at-hlevel→is-separated-at-hlevel n $ di x y

is-discrete→is-separated : is-discrete A → is-separated A
is-discrete→is-separated = is-decidable-at-hlevel→is-separated-at-hlevel 1

-- Hedberg
is-discrete→is-set : is-discrete A → is-set A
is-discrete→is-set = is-separated→is-set ∘ is-discrete→is-separated

opaque
  unfolding is-of-hlevel is-decidable-at-hlevel
  is-decidable-at-hlevel-is-prop : (n : ℕ) → is-prop (is-decidable-at-hlevel (suc n) A)
  is-decidable-at-hlevel-is-prop 0 d₁ d₂ i _ _ =
    dec-is-of-hlevel 1 (is-discrete→is-set d₁ _ _) (d₁ _ _) (d₂ _ _) i
  is-decidable-at-hlevel-is-prop (suc n) p q i x y
    = is-decidable-at-hlevel-is-prop n (p x y) (q x y) i


is-discrete-is-prop : is-prop (is-discrete A)
is-discrete-is-prop = is-decidable-at-hlevel-is-prop 0

is-discrete-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) (is-discrete A)
is-discrete-is-of-hlevel _ = is-prop→is-of-hlevel-suc is-discrete-is-prop


opaque
  unfolding is-of-hlevel is-decidable-at-hlevel
  is-decidable-at-hlevel-suc
    : (n : HLevel)
    → is-decidable-at-hlevel (suc n) A
    → is-decidable-at-hlevel (suc (suc n)) A
  is-decidable-at-hlevel-suc 0       di _ _ _ _ = yes (is-discrete→is-set di _ _ _ _)
  is-decidable-at-hlevel-suc (suc n) di x y = is-decidable-at-hlevel-suc n $ di x y

  is-of-hlevel-is-discrete : (n : HLevel) → is-discrete (is-of-hlevel n A)
  is-of-hlevel-is-discrete _ _ _ = yes (is-of-hlevel-is-prop _ _ _)

is-decidable-at-hlevel-+
  : (m n : HLevel)
  → is-decidable-at-hlevel (suc m) A
  → is-decidable-at-hlevel (suc (n + m)) A
is-decidable-at-hlevel-+ m 0       = id
is-decidable-at-hlevel-+ m 1       = is-decidable-at-hlevel-suc m
is-decidable-at-hlevel-+ m (suc n) = is-decidable-at-hlevel-suc (n + m) ∘ is-decidable-at-hlevel-+ m n

opaque
  unfolding is-decidable-at-hlevel
  is-discrete-injection : (A ↣ B) → is-discrete B → is-discrete A
  is-discrete-injection (f , f-inj) B-dis x y =
    Dec.map f-inj
            (λ ¬fp p → ¬fp (ap f p))
            (B-dis (f x) (f y))

is-discrete-embedding : (A ↪ B) → is-discrete B → is-discrete A
is-discrete-embedding (f , f-emb) =
  is-discrete-injection (f , has-prop-fibres→injective f f-emb)


-- basic automation

decide : (n : HLevel) ⦃ d : is-decidable-at-hlevel n A ⦄ → is-decidable-at-hlevel n A
decide n ⦃ d ⦄ = d

opaque
  unfolding is-of-hlevel is-decidable-at-hlevel
  Σ-is-discrete
    : {B : A → Type ℓ′}
    → is-discrete A → ((a : A) → is-discrete (B a))
    → is-discrete (Σ A B)
  Σ-is-discrete {B} A-d B-d = is-discrete-η helper where
    helper : _
    helper (a₁ , b₁) (a₂ , b₂) with A-d a₁ a₂
    ... | no  a₁≠a₂ = no λ q → a₁≠a₂ (ap fst q)
    ... | yes a₁=a₂ with B-d _ (subst _ a₁=a₂ b₁) b₂
    ... | no  b₁≠b₂ = no λ r → b₁≠b₂ $ from-pathP $
      subst (λ X → ＜ b₁ ／ (λ i → B (X i)) ＼ b₂ ＞)
            (is-discrete→is-set A-d a₁ a₂ (ap fst r) a₁=a₂)
            (ap snd r)
    ... | yes b₁=b₂ = yes $ Σ-path a₁=a₂ b₁=b₂

  ×-is-discrete
    : is-discrete A → is-discrete B
    → is-discrete (A × B)
  ×-is-discrete A-d B-d = is-discrete-η helper where
    helper : (x y : _) → Dec (x ＝ y)
    helper (a₁ , b₁) (a₂ , b₂) with A-d a₁ a₂
    ... | no  a₁≠a₂ = no λ q → a₁≠a₂ (ap fst q)
    ... | yes a₁=a₂ with B-d b₁ b₂
    ... | no  b₁≠b₂ = no λ r → b₁≠b₂ (ap snd r)
    ... | yes b₁=b₂ = yes $ Σ-pathP a₁=a₂ b₁=b₂

  lift-is-discrete
    : is-discrete A → is-discrete (Lift ℓ A)
  lift-is-discrete di (lift x) (lift y) =
      Dec.map (ap lift) (_∘ ap lower) (di x y)

  ×-decision : Decision A → Decision B → Decision (A × B)
  ×-decision da db .does = da .does and db .does
  ×-decision (no ¬a) db .proof = ofⁿ $ ¬a ∘ fst
  ×-decision (yes a) (no ¬b) .proof = ofⁿ $ ¬b ∘ snd
  ×-decision (yes a) (yes b) .proof = ofʸ (a , b)

  →-decision : Decision A → Decision B → Decision (A → B)
  →-decision da db .does = not (da .does) or db .does
  →-decision (no ¬a) db .proof = ofʸ $ λ a → absurd (¬a a)
  →-decision (yes a) (no ¬b) .proof = ofⁿ $ ¬b ∘ (_$ a)
  →-decision (yes a) (yes b) .proof = ofʸ λ _ → b
