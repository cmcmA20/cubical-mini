{-# OPTIONS --safe #-}
module Data.Dec.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Empty
open import Data.Sum.Path

open import Meta.Reflection.HLevel
open import Meta.Reflection.Record

open import Data.Dec.Base public

private variable
  ℓ ℓ′ : Level
  P A : Type ℓ
  Q : Type ℓ′
  b : Bool

dec-as-sum : Dec P ≃ ((¬ P) ⊎ P)
dec-as-sum = iso→equiv $ dec-record-iso _ ∙ᵢ reflects-as-sumᵢ
  where
  open Reflects
  module _ {ℓ} (P : Type ℓ) where
    dec-record-iso : Iso (Dec P) (Σ[ does ꞉ Bool ] Reflects P does)
    unquoteDef dec-record-iso = define-record-iso dec-record-iso (quote Dec)
  reflects-as-sumᵢ : (Σ[ b ꞉ Bool ] Reflects P b)
                   ≅ ((¬ P) ⊎ P)
  reflects-as-sumᵢ .fst (false , ofⁿ ¬p) = inl ¬p
  reflects-as-sumᵢ .fst (true  , ofʸ  p) = inr p
  reflects-as-sumᵢ .snd .is-iso.inv (inl ¬p) = false , ofⁿ ¬p
  reflects-as-sumᵢ .snd .is-iso.inv (inr  p) = true , ofʸ p
  reflects-as-sumᵢ .snd .is-iso.rinv (inl _) = refl
  reflects-as-sumᵢ .snd .is-iso.rinv (inr _) = refl
  reflects-as-sumᵢ .snd .is-iso.linv (false , ofⁿ _) = refl
  reflects-as-sumᵢ .snd .is-iso.linv (true  , ofʸ _) = refl

dec-is-of-hlevel : (n : HLevel) → is-of-hlevel n A → is-of-hlevel n (Dec A)
dec-is-of-hlevel 0 (a , _) .fst = yes a
dec-is-of-hlevel 0 (a , p) .snd (no ¬a)  = absurd (¬a a)
dec-is-of-hlevel 0 (a , p) .snd (yes a′) = ap yes (p a′)
dec-is-of-hlevel (suc 0) A-hl =
  is-of-hlevel-≃ 1 dec-as-sum (disjoint-⊎-is-prop hlevel! A-hl (λ f → f .fst (f .snd)))
dec-is-of-hlevel (suc (suc n)) A-hl =
  is-of-hlevel-≃ (suc (suc n)) dec-as-sum
    (⊎-is-of-hlevel n (λ ¬a₁ ¬a₂ → is-of-hlevel-+ n 1 hlevel!) A-hl)
