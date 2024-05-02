{-# OPTIONS --safe #-}
module Data.List.Path where

open import Meta.Prelude

open import Data.Empty.Base
open import Data.Unit.Base

open import Data.List.Base

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
decode {xs = x ∷ xs} {y ∷ ys} (p , c) = ap² _∷_ p (decode c)

code-refl-pathᴾ : {xs ys : List A} (c : Code xs ys) → ＜ code-refl xs ／ (λ i → Code xs (decode c i)) ＼ c ＞
code-refl-pathᴾ {xs = []}     {([])}   (lift tt) = refl
code-refl-pathᴾ {xs = x ∷ xs} {y ∷ ys} (p , c) i = (λ j → p (i ∧ j)) , code-refl-pathᴾ c i

identity-system : is-identity-system {A = List A} Code code-refl
identity-system .to-path      = decode
identity-system .to-path-over = code-refl-pathᴾ

code-is-of-hlevel : {xs ys : List A} {n : HLevel} → is-of-hlevel (2 + n) A → is-of-hlevel (1 + n) (Code xs ys)
code-is-of-hlevel {xs = []}     {([])}  _ = hlevel _
code-is-of-hlevel {xs = []}     {_ ∷ _} _ = hlevel _
code-is-of-hlevel {xs = _ ∷ _}  {([])}  _ = hlevel _
code-is-of-hlevel {xs = x ∷ xs} {y ∷ ys} A-hl =
  ×-is-of-hlevel _ (path-is-of-hlevel _ A-hl x y) (code-is-of-hlevel A-hl)

opaque
  list-is-of-hlevel : (n : HLevel)
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (2 + n) (List A)
  list-is-of-hlevel n A-hl _ _ =
    ≃→is-of-hlevel (1 + n)
                   (identity-system-gives-path identity-system ⁻¹)
                   (code-is-of-hlevel A-hl)

instance opaque
  H-Level-List : ∀ {n} → ⦃ A-hl : H-Level (2 + n) A ⦄ → H-Level (2 + n) (List A)
  H-Level-List {n} .H-Level.has-of-hlevel = list-is-of-hlevel _ (hlevel (2 + n))
