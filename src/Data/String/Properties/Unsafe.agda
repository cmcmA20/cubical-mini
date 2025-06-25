module Data.String.Properties.Unsafe where

open import Foundations.Base
open import Meta.Effect

open import Data.String.Base public
open import Data.String.Operations
open import Data.Char.Base
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Operations.Properties
open import Data.Nat.Base
open import Data.Maybe as Maybe

postulate
  list→string→list : {xs : List Char} → string→list (list→string xs) ＝ xs

  string→list→string : {s : String} → list→string (string→list s) ＝ s

  string→list-++ₛ : {s₁ s₂ : String} → string→list (s₁ ++ₛ s₂) ＝ string→list s₁ ++ string→list s₂

  string-uncons : {s : String} → mapₘ (second string→list) (uncons s) ＝ unconsᵐ (string→list s)

lengthₛ-++ₛ : {s₁ s₂ : String} → lengthₛ (s₁ ++ₛ s₂) ＝ lengthₛ s₁ + lengthₛ s₂
lengthₛ-++ₛ {s₁} {s₂} =
    ap length (string→list-++ₛ {s₁})
  ∙ ++-length (string→list s₁) (string→list s₂)

string-tailₛ : {s : String} → mapₘ string→list (tailₛ s) ＝ tailᵐ (string→list s)
string-tailₛ {s} =
    happly (map-pres-comp {M = eff Maybe} ⁻¹ ∙ map-pres-comp {M = eff Maybe})
           (uncons s)
  ∙ ap (mapₘ snd) (string-uncons {s = s})

length-tailₛ : {s : String} → lengthₛ s ＝ Maybe.rec zero (suc ∘ lengthₛ) (tailₛ s)
length-tailₛ {s} =
      length-tailᵐ
    ∙ ap (Maybe.rec zero (suc ∘ length)) (string-tailₛ {s = s} ⁻¹)
    ∙ mapₘ-rec {m = tailₛ s}
