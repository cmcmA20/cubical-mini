{-# OPTIONS --safe #-}
module Correspondences.Discrete where

open import Foundations.Base
open import Foundations.HLevel.Base

open import Correspondences.Base public
open import Correspondences.Decidable
open import Correspondences.Separated

open import Data.Dec.Base as Dec
open import Data.Dec.Path

open import Functions.Embedding

private variable
  ℓ ℓ′ : Level
  A : Type ℓ
  B : Type ℓ′

opaque
  is-discrete : Type ℓ → Type ℓ
  is-discrete = Dec on-paths-of_

  is-discrete-β : is-discrete A → Dec on-paths-of A
  is-discrete-β = id

  is-discrete-η : Dec on-paths-of A → is-discrete A
  is-discrete-η = id

  opaque
    unfolding is-separated
    is-discrete→is-separated : is-discrete A → is-separated A
    is-discrete→is-separated di _ _ = dec→essentially-classical (di _ _)

-- Hedberg
is-discrete→is-set : is-discrete A → is-set A
is-discrete→is-set = is-separated→is-set ∘ is-discrete→is-separated

opaque
  unfolding is-of-hlevel is-discrete
  is-discrete-is-prop : is-prop (is-discrete A)
  is-discrete-is-prop d₁ d₂ i _ _ =
    dec-is-of-hlevel 1 (is-discrete→is-set d₁ _ _) (d₁ _ _) (d₂ _ _) i

is-discrete-is-of-hlevel : (n : HLevel) → is-of-hlevel (suc n) (is-discrete A)
is-discrete-is-of-hlevel _ = is-prop→is-of-hlevel-suc is-discrete-is-prop

is-discrete-injection : (A ↣ B) → is-discrete B → is-discrete A
is-discrete-injection (f , f-inj) B-dis = is-discrete-η λ x y →
  Dec.map f-inj
          (λ ¬fp p → ¬fp (ap f p))
          (is-discrete-β B-dis (f x) (f y))

is-discrete-embedding : (A ↪ B) → is-discrete B → is-discrete A
is-discrete-embedding (f , f-emb) =
  is-discrete-injection (f , has-prop-fibres→injective f f-emb)


discrete : ⦃ d : is-discrete A ⦄ → is-discrete A
discrete ⦃ d ⦄ = d

Σ-is-discrete
  : {B : A → Type ℓ′}
  → is-discrete A → (Π[ a ꞉ A ] is-discrete (B a))
  → is-discrete (Σ[ a ꞉ A ] B a)
Σ-is-discrete {B} A-d B-d = is-discrete-η helper where
  helper : _
  helper (a₁ , b₁) (a₂ , b₂) with is-discrete-β A-d a₁ a₂
  ... | no  a₁≠a₂ = no λ q → a₁≠a₂ (ap fst q)
  ... | yes a₁=a₂ with is-discrete-β (B-d _) (subst _ a₁=a₂ b₁) b₂
  ... | no  b₁≠b₂ = no λ r → b₁≠b₂ $ from-pathP $
    subst (λ X → ＜ b₁ ／ (λ i → B (X i)) ＼ b₂ ＞)
          (is-set-β (is-discrete→is-set A-d) a₁ a₂ (ap fst r) a₁=a₂)
          (ap snd r)
  ... | yes b₁=b₂ = yes $ Σ-path a₁=a₂ b₁=b₂

×-is-discrete : is-discrete A → is-discrete B
              → is-discrete (A × B)
×-is-discrete A-d B-d = is-discrete-η helper where
  helper : (x y : _) → Dec (x ＝ y)
  helper (a₁ , b₁) (a₂ , b₂) with is-discrete-β A-d a₁ a₂
  ... | no  a₁≠a₂ = no λ q → a₁≠a₂ (ap fst q)
  ... | yes a₁=a₂ with is-discrete-β B-d b₁ b₂
  ... | no  b₁≠b₂ = no λ r → b₁≠b₂ (ap snd r)
  ... | yes b₁=b₂ = yes $ Σ-pathP a₁=a₂ b₁=b₂

lift-is-discrete : is-discrete A → is-discrete (Lift ℓ A)
lift-is-discrete di = is-discrete-η λ (lift x) (lift y) →
    Dec.map (ap lift) (_∘ ap lower) (is-discrete-β di x y)
