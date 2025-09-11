{-# OPTIONS --safe #-}
module Data.Nat.Two.Properties where

open import Foundations.HLevel
open import Foundations.Sigma
open import Meta.Prelude
open Variadics _

open import Data.Empty.Properties
open import Data.Bool.Base as Bool
open import Data.Bool.Properties
open import Data.Reflects.Base
open import Data.Dec.Base as Dec
open import Data.Nat.Base as Nat
open import Data.Nat.Path
open import Data.Nat.Two
open import Data.Nat.Properties
open import Data.Nat.Order.Base
open import Data.Truncation.Propositional.Base
open import Data.Truncation.Propositional.Properties
open import Data.Sum.Base
open import Data.Sum.Path
open import Data.Sum.Properties

bit-and : ∀ x y → bit (x and y) ＝ bit x · bit y
bit-and false y = refl
bit-and true  y = sym $ +-zero-r (bit y)

bit-compl : ∀ x → bit x + bit (not x) ＝ 1
bit-compl false = refl
bit-compl true  = refl

odd-+ : ∀ m n → odd (m + n) ＝ odd m xor odd n
odd-+  zero   n = refl
odd-+ (suc m) n = ap not (odd-+ m n) ∙ sym (xor-assoc true (odd m) (odd n))

odd-· : ∀ m n → odd (m · n) ＝ odd m and odd n
odd-·  zero   n = refl
odd-· (suc m) n = odd-+ n (m · n)
                ∙ ap (odd n xor_) (odd-· m n)
                ∙ sym (and-distrib-xor-r true (odd m) (odd n))

+-×2 : ∀ n → n ×2 ＝ n + n
+-×2  zero   = refl
+-×2 (suc n) = ap (suc ∘ suc) (+-×2 n) ∙ ap suc (sym (+-suc-r n n))

cancel-×-÷ : ∀ n → n ×2 ÷2 ＝ n
cancel-×-÷  zero   = refl
cancel-×-÷ (suc n) = ap suc (cancel-×-÷ n)

cancel-×-÷↑ : ∀ n → n ×2 ÷2↑ ＝ n
cancel-×-÷↑  zero   = refl
cancel-×-÷↑ (suc n) = ap suc (cancel-×-÷↑ n)

÷↑-÷ : ∀ n → n ÷2↑ ＝ n ÷2 + bit (odd n)
÷↑-÷  zero   = refl
÷↑-÷ (suc n) = +-comm 1 (n ÷2)
             ∙ ap ((n ÷2) +_) (sym (bit-compl (odd n)))
             ∙ +-assoc (n ÷2) (bit (odd n)) (bit (not (odd n)))
             ∙ ap (_+ bit (not (odd n))) (sym $ ÷↑-÷ n)

bit-÷-× : ∀ n → bit (odd n) + n ÷2 ×2 ＝ n
bit-÷-×  zero   = refl
bit-÷-× (suc n) =
    ap (λ q → bit (even n) + q ×2) (÷↑-÷ n)
  ∙ ap (bit (even n) +_) (  ·-distrib-+-r (n ÷2) (bit (odd n)) 2
                          ∙ +-comm ((n ÷2) ×2) ((bit (odd n)) ×2))
  ∙ +-assoc (bit (even n)) ((bit (odd n)) ×2) ((n ÷2) ×2)
  ∙ ap (_+ (n ÷2) ×2) (  ap (bit (even n) +_) (·-comm (bit (odd n)) 2)
                       ∙ +-assoc (bit (even n)) (bit (odd n)) (bit (odd n) + 0)
                       ∙ ap² _+_ (  +-comm (bit (even n)) (bit (odd n))
                                  ∙ bit-compl (odd n))
                                 (+-zero-r (bit (odd n))))
  ∙ ap suc (bit-÷-× n)

-- order

≤-×2 : ∀ m n → (m ×2 ≤ n ×2) ≃ (m ≤ n)
≤-×2 m n =
    ≤≃≤·r {m = m} {n = n}
  ∙ (is-prop≃equiv-∥-∥₁ $
     disjoint-⊎-is-prop (hlevel 1 ⦃ x = H-Level-Pathᴾ ⦄) -- TODO why?
                        (hlevel 1)
                        (false! $²_)) ⁻¹
  ∙ ⊎-ap-l (¬→≃⊥ false!)
  ∙ ⊎-zero-l

<-×2 : ∀ m n → (m ×2 < n ×2) ≃ (m < n)
<-×2 m n = <≃≱ ∙ ≃→¬≃ (≤-×2 n m) ∙ <≃≱ ⁻¹

≤-÷×2 : ∀ m n → (m ≤ n ÷2) ≃ (m ×2 ≤ n)
≤-÷×2 m n =
    Bool.elim {P = λ q → m ≤ (n ÷2) ≃ (m ×2) ≤ bit q + ((n ÷2) ×2)}
              (Nat.elim (λ q → q ≤ (n ÷2) ≃ (q ×2) ≤ suc ((n ÷2) ×2))
                        (prop-extₑ! (λ _ → z≤) λ _ → z≤)
                        (λ {n = m} _ → <≃suc≤ ∙ <-×2 m (n ÷2) ⁻¹ ∙ <≃suc≤ ⁻¹ ∙ ≤≃≤+l)
                        m)
              (≤-×2 m (n ÷2) ⁻¹)
              (odd n)
  ∙ =→≃ (ap (m ×2 ≤_) (bit-÷-× n))

<-÷×2 : ∀ m n → (m ÷2 < n) ≃ (m < n ×2)
<-÷×2 m n = <≃≱ ∙ ≃→¬≃ (≤-÷×2 n m) ∙ <≃≱ ⁻¹
