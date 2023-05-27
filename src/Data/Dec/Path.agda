{-# OPTIONS --safe #-}
module Data.Dec.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Data.Empty
open import Data.Sum

open import Meta.Reflection.HLevel
open import Meta.Reflection.Record

open import Data.Dec.Base public

private variable
  ℓ ℓ′ : Level
  P A : Type ℓ
  Q : Type ℓ′
  b : Bool

Dec≃⊎ : Dec P ≃ ((¬ P) ⊎ P)
Dec≃⊎ = iso→equiv $ dec-record-iso _ ∙ᵢ reflects-as-sumᵢ
  where
  open Reflects
  module _ {ℓ} (P : Type ℓ) where
    dec-record-iso : Iso (Dec P) (Σ[ does ꞉ Bool ] Reflects P does)
    unquoteDef dec-record-iso = define-record-iso dec-record-iso (quote Dec)
  reflects-as-sumᵢ : (Σ[ b ꞉ Bool ] Reflects P b)
                   ≅ ((¬ P) ⊎ P)
  reflects-as-sumᵢ .fst (false , ofⁿ ¬p) = inj-l ¬p
  reflects-as-sumᵢ .fst (true  , ofʸ  p) = inj-r p
  reflects-as-sumᵢ .snd .is-iso.inv (inj-l ¬p) = false , ofⁿ ¬p
  reflects-as-sumᵢ .snd .is-iso.inv (inj-r  p) = true , ofʸ p
  reflects-as-sumᵢ .snd .is-iso.rinv (inj-l _) = refl
  reflects-as-sumᵢ .snd .is-iso.rinv (inj-r _) = refl
  reflects-as-sumᵢ .snd .is-iso.linv (false , ofⁿ _) = refl
  reflects-as-sumᵢ .snd .is-iso.linv (true  , ofʸ _) = refl

Dec-is-of-hlevel : (n : HLevel) → is-of-hlevel n A → is-of-hlevel n (Dec A)
Dec-is-of-hlevel 0𝒽 (a , _) .fst = yes a
Dec-is-of-hlevel 0𝒽 (a , p) .snd (no ¬a)  = absurd (¬a a)
Dec-is-of-hlevel 0𝒽 (a , p) .snd (yes a′) = ap yes (p a′)
Dec-is-of-hlevel (𝒽suc 0𝒽) A-hl =
  is-of-hlevel-≃ 1 Dec≃⊎ (disjoint-⊎-is-prop hlevel! A-hl (λ f → f .fst (f .snd)))
Dec-is-of-hlevel (𝒽suc (𝒽suc n)) A-hl =
  is-of-hlevel-≃ (suc (suc n)) Dec≃⊎
    (⊎-is-hlevel n (λ ¬a₁ ¬a₂ → is-of-hlevel-+ n 1 hlevel!) A-hl)
