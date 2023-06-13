{-# OPTIONS --safe #-}
module Data.List.Path where

open import Foundations.Base
open import Foundations.Equiv

open import Meta.Reflection.HLevel

open import Structures.IdentitySystem.Base

open import Correspondences.Nullary.Negation

open import Data.Empty
open import Data.Unit

open import Data.List.Base public

private variable
  ℓ ℓ′ : Level
  n : HLevel
  A : Type ℓ
  x y : A
  xs ys : List A

∷-head-inj : x ∷ xs ＝ y ∷ ys → x ＝ y
∷-head-inj {x} = ap (head x)

∷-tail-inj : x ∷ xs ＝ y ∷ ys → xs ＝ ys
∷-tail-inj = ap tail

∷≠[] : ¬ (x ∷ xs) ＝ []
∷≠[] p = subst discrim p tt
  where
  discrim : List _ → Type
  discrim []      = ⊥
  discrim (_ ∷ _) = ⊤

module List-path-code where

  Code : List A → List A → Type (level-of-type A)
  Code []       []       = Lift _ ⊤
  Code []       (y ∷ ys) = Lift _ ⊥
  Code (x ∷ xs) []       = Lift _ ⊥
  Code (x ∷ xs) (y ∷ ys) = (x ＝ y) × Code xs ys

  code-refl : (xs : List A) → Code xs xs
  code-refl []       = lift tt
  code-refl (_ ∷ xs) = refl , code-refl xs

  decode : Code xs ys → xs ＝ ys
  decode {xs = []}     {([])}   _       = refl
  decode {xs = x ∷ xs} {y ∷ ys} (p , c) = ap₂ _∷_ p (decode c)

  code-refl-pathP : {xs ys : List A} (c : Code xs ys) → ＜ code-refl xs ／ (λ i → Code xs (decode c i)) ＼ c ＞
  code-refl-pathP {xs = []}     {([])}   (lift tt) = refl
  code-refl-pathP {xs = x ∷ xs} {y ∷ ys} (p , c) i = (λ j → p (i ∧ j)) , code-refl-pathP c i

  list-identity-system : is-identity-system {A = List A} Code code-refl
  list-identity-system .to-path      = decode
  list-identity-system .to-path-over = code-refl-pathP

  code-is-of-hlevel : {xs ys : List A} {n : HLevel} → is-of-hlevel (2 + n) A → is-of-hlevel (1 + n) (Code xs ys)
  code-is-of-hlevel {xs = []}     {([])}  _ = hlevel!
  code-is-of-hlevel {xs = []}     {_ ∷ _} _ = hlevel!
  code-is-of-hlevel {xs = _ ∷ _}  {([])}  _ = hlevel!
  code-is-of-hlevel {xs = x ∷ xs} {y ∷ ys} A-hl =
    ×-is-of-hlevel _ (path-is-of-hlevel′ _ A-hl x y) (code-is-of-hlevel A-hl)

open List-path-code

list-is-of-hlevel : (n : HLevel)
                  → is-of-hlevel (2 + n) A
                  → is-of-hlevel (2 + n) (List A)
list-is-of-hlevel n A-hl _ _ =
  is-of-hlevel-≃ (1 + n)
                 (identity-system-gives-path list-identity-system ₑ⁻¹)
                 (code-is-of-hlevel A-hl)
