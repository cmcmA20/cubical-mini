{-# OPTIONS --safe #-}
module Data.Dec.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Extensionality
open import Meta.Search.HLevel

open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Sum.Path

open import Data.Dec.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

dec-as-sum : Dec A ≃ ((¬ A) ⊎ A)
dec-as-sum = ≅→≃ helper where
  helper : Iso _ _
  helper .fst (yes a) = inr  a
  helper .fst (no ¬a) = inl ¬a
  helper .snd .is-iso.inv (inl ¬a) = no ¬a
  helper .snd .is-iso.inv (inr  a) = yes a
  helper .snd .is-iso.rinv (inl ¬a) = refl
  helper .snd .is-iso.rinv (inr  a) = refl
  helper .snd .is-iso.linv (no ¬a) = refl
  helper .snd .is-iso.linv (yes a) = refl

opaque
  unfolding is-of-hlevel
  dec-contr : is-contr A → is-contr (Dec A)
  dec-contr (a , _) .fst = yes a
  dec-contr (a , p) .snd (no ¬a)  = absurd (¬a a)
  dec-contr (a , p) .snd (yes a′) = ap yes (p a′)

dec-is-of-hlevel : (n : HLevel) → is-of-hlevel n A → is-of-hlevel n (Dec A)
dec-is-of-hlevel 0 = dec-contr
dec-is-of-hlevel 1 A-hl =
  ≃→is-of-hlevel 1 dec-as-sum (disjoint-⊎-is-prop hlevel! A-hl (λ f → f .fst (f .snd)))
dec-is-of-hlevel (suc (suc n)) A-hl =
 ≃→is-of-hlevel (suc (suc n)) dec-as-sum (⊎-is-of-hlevel n hlevel! A-hl)

instance
  decomp-hlevel-dec : goal-decomposition (quote is-of-hlevel) (Dec A)
  decomp-hlevel-dec = decomp (quote dec-is-of-hlevel) [ `level-same , `search (quote is-of-hlevel) ]

instance
  Extensional-Dec : ⦃ sa : Extensional A ℓ′ ⦄ → Extensional (Dec A) ℓ′
  Extensional-Dec ⦃ sa ⦄ .Pathᵉ (_ because ofʸ p) (_ because ofʸ q) = Pathᵉ sa p q
  Extensional-Dec        .Pathᵉ (_ because ofⁿ _) (_ because ofⁿ _) = Lift _ ⊤
  Extensional-Dec        .Pathᵉ _                 _                 = Lift _ ⊥
  Extensional-Dec ⦃ sa ⦄ .reflᵉ (_ because ofʸ p) = reflᵉ sa p
  Extensional-Dec        .reflᵉ (_ because ofⁿ _) = _
  Extensional-Dec ⦃ sa ⦄ .idsᵉ .to-path {a = _ because ofʸ a} {b = _ because ofʸ b} =
    ap yes ∘ sa .idsᵉ .to-path
  Extensional-Dec        .idsᵉ .to-path {a = _ because ofⁿ a} {b = _ because ofⁿ _} _ =
    ap no prop!
  Extensional-Dec ⦃ sa ⦄ .idsᵉ .to-path-over {_ because ofʸ _} {_ because ofʸ _} =
    sa .idsᵉ .to-path-over
  Extensional-Dec        .idsᵉ .to-path-over {_ because ofⁿ _} {_ because ofⁿ _} _ = refl
