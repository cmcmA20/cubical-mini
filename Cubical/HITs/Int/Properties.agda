{-# OPTIONS --safe #-}
module Cubical.HITs.Int.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat using (ℕ; zero; suc; +-zero; +-suc; +-comm)
  renaming (_+_ to _+ₙ_)
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

isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ

plusSlow : ℤ → ℤ → ℤ
plusSlow m n = invEquiv ℤ≃ℤᵢ .fst (ℤ≃ℤᵢ .fst m +ᵢ ℤ≃ℤᵢ .fst n)

⊖-right-zero : ∀ m → m ⊖ 0 ≡ pos m
⊖-right-zero zero    = 0₋≡0₊
⊖-right-zero (suc _) = refl

[-_+_] : ℕ → ℤ → ℤ
[- ∣m∣ + n ] = elim (λ ∣n∣ → neg (∣m∣ +ₙ ∣n∣))
                    (λ ∣n∣ → ∣n∣ ⊖ ∣m∣)
                    (cong neg (+-zero _))
                    n

[+_+_] : ℕ → ℤ → ℤ
[+ ∣m∣ + n ] = elim (λ ∣n∣ → ∣m∣ ⊖ ∣n∣)
                    (λ ∣n∣ → pos (∣m∣ +ₙ ∣n∣))
                    (⊖-right-zero ∣m∣ ∙ cong pos (sym (+-zero ∣m∣)))
                    n

zeroCompatible : ∀ n → [- 0 + n ] ≡ [+ 0 + n ]
zeroCompatible = elim-prop (λ _ → refl) (λ _ → ⊖-right-zero _) (isSetℤ _ _)

_+_ : ℤ → ℤ → ℤ
m + n = elim (λ ∣m∣ → [- ∣m∣ + n ]) (λ ∣m∣ → [+ ∣m∣ + n ]) (zeroCompatible n) m

@0 ℤ≡ℤᵢ : ℤ ≡ ℤᵢ
ℤ≡ℤᵢ = ua ℤ≃ℤᵢ

succEquiv : ℤ ≃ ℤ
succEquiv = isoToEquiv (iso succ pred succPred predSucc)
  where
  succPred : ∀ m → succ (pred m) ≡ m
  succPred (neg _)       = refl
  succPred (pos zero)    = 0₋≡0₊
  succPred (pos (suc _)) = refl
  succPred (0₋≡0₊ i) j = 0₋≡0₊ (i ∧ j)

  predSucc : ∀ m → pred (succ m) ≡ m
  predSucc (neg zero)    = sym 0₋≡0₊
  predSucc (neg (suc _)) = refl
  predSucc (pos _)       = refl
  predSucc (0₋≡0₊ i) j = sym 0₋≡0₊ (~ i ∧ j)

succEquiv′ : ℤ ≃ ℤ
succEquiv′ = isoToEquiv (iso succ pred succPred predSucc)
  where
  succPred : ∀ m → succ (pred m) ≡ m
  succPred = elim-prop (λ _ → refl)
                       (λ { zero → 0₋≡0₊
                          ; (suc _) → refl } )
                       (isSetℤ _ _)

  predSucc : ∀ m → pred (succ m) ≡ m
  predSucc = elim-prop (λ { zero    → sym 0₋≡0₊
                          ; (suc _) → refl } )
                       (λ _ → refl)
                       (isSetℤ _ _)

module Homo where
  fromℤᵢ = invEquiv ℤ≃ℤᵢ .fst

  preserveZero : fromℤᵢ (pos 0) ≡ pos 0
  preserveZero = refl

  preserveSucc : ∀ m → fromℤᵢ (sucℤ m) ≡ succ (fromℤᵢ m)
  preserveSucc (pos n) = refl
  preserveSucc (negsuc zero) = sym 0₋≡0₊
  preserveSucc (negsuc (suc _)) = refl

  preservePred : ∀ m → fromℤᵢ (predℤ m) ≡ pred (fromℤᵢ m)
  preservePred (pos zero) = refl
  preservePred (pos (suc _)) = refl
  preservePred (negsuc _) = refl

  minusSucc : ∀ m n → (m ⊖ suc n) ≡ pred (m ⊖ n)
  minusSucc zero _ = refl
  minusSucc (suc m) zero = ⊖-right-zero _
  minusSucc (suc m) (suc n) = minusSucc m n

  preservePlus : ∀ m n → fromℤᵢ (m +ᵢ n) ≡ fromℤᵢ m + fromℤᵢ n
  preservePlus (pos 0) (pos 0) = refl
  preservePlus (pos 0) (pos (suc n)) = let ih = preservePlus (pos 0) (pos n)
    in preserveSucc _ ∙ cong succ ih
  preservePlus (pos (suc m)) (pos 0) = cong (λ f → pos (suc f)) (sym $ +-zero m)
  preservePlus (pos (suc m)) (pos (suc n)) = let ih = preservePlus (pos (suc m)) (pos n)
    in preserveSucc _ ∙ cong succ ih ∙ cong (λ f → pos (suc f)) (sym $ +-suc m n)
  preservePlus (pos 0) (negsuc n) = cong fromℤᵢ $ sym $ pos0+ (negsuc n)
  preservePlus (pos (suc m)) (negsuc n) = let ih = preservePlus (pos m) (negsuc n)
    in cong fromℤᵢ (sym $ sucℤ+ (pos m) (negsuc n)) ∙ preserveSucc _ ∙ cong succ (ih ∙ minusSucc m n) ∙ secEq succEquiv _
  preservePlus (negsuc m) (pos 0) = refl
  preservePlus (negsuc m) (pos (suc n)) = let ih = preservePlus (negsuc m) (pos n)
    in preserveSucc _ ∙ cong succ (ih ∙ minusSucc n m) ∙ secEq succEquiv _
  preservePlus (negsuc m) (negsuc 0) = cong (λ f → neg (suc f)) (+-comm 1 _)
  preservePlus (negsuc m) (negsuc (suc n)) = let ih = preservePlus (negsuc m) (negsuc n)
    in preservePred _ ∙ cong pred ih ∙ cong (λ f → neg (suc f)) (sym $ +-suc _ _)
