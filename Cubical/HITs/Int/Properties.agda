{-# OPTIONS --safe #-}
module Cubical.HITs.Int.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat using (ℕ; zero; suc; +-zero) renaming (_+_ to _+ₙ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int
  renaming ( ℤ to ℤᵢ; neg to negᵢ; _+_ to _+ᵢ_
           ; isSetℤ to isSetℤᵢ
           ; discreteℤ to discreteℤᵢ )

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.Int.Base

open import Cubical.Relation.Nullary

open import Cubical.Instances.HLevels

ℤ≃ℤᵢ : ℤ ≃ ℤᵢ
ℤ≃ℤᵢ = isoToEquiv (iso to from li ri)
  where
  to : ℤ → ℤᵢ
  to (neg zero)    = pos 0
  to (neg (suc n)) = negsuc n
  to (pos n)       = pos n
  to (0₋≡0₊ _) = pos zero

  from : ℤᵢ → ℤ
  from (pos    n) = pos n
  from (negsuc n) = neg (suc n)

  li : (b : ℤᵢ) → to (from b) ≡ b
  li (pos _)    = refl
  li (negsuc _) = refl

  ri : (a : ℤ) → from (to a) ≡ a
  ri (neg zero)    = sym 0₋≡0₊
  ri (neg (suc _)) = refl
  ri (pos _)       = refl
  ri (0₋≡0₊ i) j = 0₋≡0₊ (i ∨ ~ j)

discreteℤ : Discrete ℤ
discreteℤ = EquivPresDiscrete (invEquiv ℤ≃ℤᵢ) discreteℤᵢ

-- discrete′ℤ : Discrete ℤ
-- discrete′ℤ m n =
--   elim-prop {B = λ m → Dec (m ≡ n)}
--             (λ ∣m∣ → elim-prop {B = λ n → Dec (neg ∣m∣ ≡ n)} (λ ∣n∣ → {!!}) (λ ∣n∣ → no {!!}) {!!} n)
--             (λ ∣m∣ → {!!})
--             (isPropDec (isOfHLevelRespectEquiv 2 (invEquiv ℤ≃ℤᵢ) isSetℤᵢ _ _))
--             m

isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ

plus : ℤ → ℤ → ℤ
plus m n = invEquiv ℤ≃ℤᵢ .fst (ℤ≃ℤᵢ .fst m +ᵢ ℤ≃ℤᵢ .fst n)

⊖-right-zero : ∀ m → m ⊖ 0 ≡ pos m
⊖-right-zero zero    = 0₋≡0₊
⊖-right-zero (suc _) = refl

⊖′-right-zero : ∀ m → m ⊖′ 0 ≡ pos m
⊖′-right-zero zero    = 0₋≡0₊
⊖′-right-zero (suc _) = refl

bek : ℕ → ℤ → ℤ
bek ∣m∣ n = elim (λ ∣n∣ → neg (∣m∣ +ₙ ∣n∣))
                 (λ ∣n∣ → ∣n∣ ⊖ ∣m∣)
                 (cong neg (+-zero _))
                 n

bek′ : ℕ → ℤ → ℤ
bek′ ∣m∣ n = elim (λ ∣n∣ → neg (∣m∣ +ₙ ∣n∣))
                  (λ ∣n∣ → ∣n∣ ⊖′ ∣m∣)
                  (cong neg (+-zero _))
                  n

keb : ℕ → ℤ → ℤ
keb ∣m∣ n = elim (λ ∣n∣ → ∣m∣ ⊖ ∣n∣)
                 (λ ∣n∣ → pos (∣m∣ +ₙ ∣n∣))
                 (⊖-right-zero ∣m∣ ∙ cong pos (sym (+-zero ∣m∣)))
                 n

keb′ : ℕ → ℤ → ℤ
keb′ ∣m∣ n = elim (λ ∣n∣ → ∣m∣ ⊖′ ∣n∣)
                  (λ ∣n∣ → pos (∣m∣ +ₙ ∣n∣))
                  (⊖′-right-zero ∣m∣ ∙ cong pos (sym (+-zero ∣m∣)))
                  n

woow : ∀ n → bek 0 n ≡ keb 0 n
woow = elim-prop (λ _ → refl) (λ _ → ⊖-right-zero _) (isSetℤ _ _)

woow′ : ∀ n → bek′ 0 n ≡ keb′ 0 n
woow′ = elim-prop (λ _ → refl) (λ _ → ⊖′-right-zero _) (isSetℤ _ _)

_+_ : ℤ → ℤ → ℤ
m + n = elim (λ ∣m∣ → bek ∣m∣ n) (λ ∣m∣ → keb ∣m∣ n) (woow n) m

_+′_ : ℤ → ℤ → ℤ
m +′ n = elim (λ ∣m∣ → bek′ ∣m∣ n) (λ ∣m∣ → keb′ ∣m∣ n) (woow′ n) m

@0 ℤ≡ℤᵢ : ℤ ≡ ℤᵢ
ℤ≡ℤᵢ = ua ℤ≃ℤᵢ

bya : ∀ x y → transport (λ i → ℤ≡ℤᵢ i → ℤ≡ℤᵢ i → ℤ≡ℤᵢ i) _+′_ x y ≡ x +ᵢ y
bya (pos m)    (pos n)    = pos+ m n
bya (pos m)    (negsuc n) = {!!}
bya (negsuc m) (pos n)    = {!!}
bya (negsuc m) (negsuc n) = negsuc+ m (suc n)

@0 look : PathP (λ i → (ℤ≡ℤᵢ i) → (ℤ≡ℤᵢ i) → (ℤ≡ℤᵢ i)) _+′_ _+ᵢ_
look = toPathP $ funExt₂ bya

open import Cubical.Foundations.CartesianKanOps
@0 +-comm : ∀ m n → m + n ≡ n + m
+-comm m n =
  let
    coe′ = coe0→i (λ i → ℤ≡ℤᵢ i)
    w = look
  in {!!}

-- succEquiv : ℤ ≃ ℤ
-- succEquiv = isoToEquiv (iso succ pred succPred predSucc)
--   where
--   succPred : ∀ m → succ (pred m) ≡ m
--   succPred (neg _)       = refl
--   succPred (pos zero)    = 0₋≡0₊
--   succPred (pos (suc _)) = refl
--   succPred (0₋≡0₊ i) j = 0₋≡0₊ (i ∧ j)

--   predSucc : ∀ m → pred (succ m) ≡ m
--   predSucc (neg zero)    = sym 0₋≡0₊
--   predSucc (neg (suc _)) = refl
--   predSucc (pos _)       = refl
--   predSucc (0₋≡0₊ i) j = sym 0₋≡0₊ (~ i ∧ j)

-- succEquiv′ : ℤ ≃ ℤ
-- succEquiv′ = isoToEquiv (iso succ pred succPred predSucc)
--   where
--   succPred : ∀ m → succ (pred m) ≡ m
--   succPred = elim-prop (λ _ → refl) (λ { zero → 0₋≡0₊ ; (suc _) → refl })

--   predSucc : ∀ m → pred (succ m) ≡ m
--   predSucc = elim-prop (λ { zero → sym 0₋≡0₊ ; (suc _) → refl }) (λ _ → refl)
