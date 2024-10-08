{-# OPTIONS --safe #-}
module Data.Nat.Two.Properties where

open import Foundations.Base

open import Data.Bool.Base
open import Data.Bool.Properties
open import Data.Nat.Base
open import Data.Nat.Two
open import Data.Nat.Properties

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
