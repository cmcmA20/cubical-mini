{-# OPTIONS --safe --no-exact-split #-}
module Data.List.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base
open import Data.List.Base
open import Data.Reflects.Base as Reflects
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓᵃ : Level
  n : HLevel
  A : Type ℓᵃ
  x y : A
  xs ys : List A
  b₁ b₂ : Bool

∷-head-inj : x ∷ xs ＝ y ∷ ys → x ＝ y
∷-head-inj {x} = ap (head x)

∷-tail-inj : x ∷ xs ＝ y ∷ ys → xs ＝ ys
∷-tail-inj = ap tail

module _ {A : 𝒰 ℓᵃ} ⦃ sa : Extensional A ℓ ⦄ where
  Code-List : List A → List A → 𝒰 ℓ
  Code-List []       []       = ⊤
  Code-List (x ∷ xs) (y ∷ ys) = sa .Pathᵉ x y × Code-List xs ys
  Code-List _ _ = ⊥

  code-list-refl : (xs : List A) → Code-List xs xs
  code-list-refl []       = _
  code-list-refl (x ∷ xs) = sa .reflᵉ x , code-list-refl xs

  decode-list : Code-List xs ys → xs ＝ ys
  decode-list {xs = []}     {([])}   _       = refl
  decode-list {xs = x ∷ xs} {y ∷ ys} (p , c) = ap² _∷_ (sa .idsᵉ .to-path p) (decode-list c)

  code-list-reflᴾ
    : (c : Code-List xs ys)
    → code-list-refl xs ＝[ ap (Code-List xs) (decode-list c) ]＝ c
  code-list-reflᴾ {xs = []}     {([])}   _       = refl
  code-list-reflᴾ {xs = x ∷ xs} {y ∷ ys} (p , c) = sa .idsᵉ .to-path-over p ,ₚ code-list-reflᴾ c

  instance
    Extensional-List : Extensional (List A) ℓ
    Extensional-List .Pathᵉ = Code-List
    Extensional-List .reflᵉ = code-list-refl
    Extensional-List .idsᵉ .to-path = decode-list
    Extensional-List .idsᵉ .to-path-over = code-list-reflᴾ

opaque
  code-list-is-of-hlevel
    : {n : HLevel} {xs ys : List A} → is-of-hlevel (2 + n) A → is-of-hlevel (1 + n) (Code-List xs ys)
  code-list-is-of-hlevel {xs = []}     {([])}   _  = hlevel _
  code-list-is-of-hlevel {xs = x ∷ xs} {y ∷ ys} hl =
    ×-is-of-hlevel _ (hl x y) (code-list-is-of-hlevel {xs = xs} hl)
  code-list-is-of-hlevel {xs = []}     {_ ∷ _}  _  = hlevel _
  code-list-is-of-hlevel {xs = x ∷ xs} {([])}   _  = hlevel _

  list-is-of-hlevel : (n : HLevel)
                    → is-of-hlevel (2 + n) A
                    → is-of-hlevel (2 + n) (List A)
  list-is-of-hlevel n A-hl xs _ =
    ≃→is-of-hlevel (1 + n)
                   (identity-system-gives-path (Extensional-List .idsᵉ) ⁻¹)
                   (code-list-is-of-hlevel {xs = xs} A-hl)

instance opaque
  H-Level-List : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → ⦃ A-hl : H-Level n A ⦄ → H-Level n (List A)
  H-Level-List {n} ⦃ s≤ʰs (s≤ʰs _) ⦄ .H-Level.has-of-hlevel = list-is-of-hlevel _ (hlevel n)
  {-# OVERLAPPING H-Level-List #-}

instance
  Reflects-∷≠[] : Reflects (x ∷ xs ＝ []) false
  Reflects-∷≠[] = ofⁿ λ p → ¬-so-false (subst So (ap is-cons? p) oh)

  Reflects-[]≠∷ : Reflects ([] ＝ x ∷ xs) false
  Reflects-[]≠∷ = ofⁿ λ p → ¬-so-false (subst So (ap is-nil? p) oh)

  Reflects-∷=∷ : ⦃ rh : Reflects (x ＝ y) b₁ ⦄ ⦃ rt : Reflects (xs ＝ ys) b₂ ⦄ → Reflects (x ∷ xs ＝ y ∷ ys) (b₁ and b₂)
  Reflects-∷=∷ = Reflects.dmap (λ p → ap² _∷_ (p .fst) (p .snd)) (contra < ∷-head-inj , ∷-tail-inj >) auto

  List-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (List A)
  List-is-discrete {x = []}     {([])}   = true because auto
  List-is-discrete {x = []}     {_ ∷ _}  = false because auto
  List-is-discrete {x = _ ∷ _}  {([])}   = false because auto
  List-is-discrete {x = x ∷ xs} {y ∷ ys} .does  = (x =? y) and ⌊ List-is-discrete {x = xs} {y = ys} ⌋
  List-is-discrete {x = x ∷ xs} {y ∷ ys} .proof = Reflects-∷=∷ ⦃ auto ⦄ ⦃ List-is-discrete {x = xs} {y = ys} .proof ⦄

opaque
  ∷≠[] : x ∷ xs ≠ []
  ∷≠[] = false!

opaque
  []≠∷ : [] ≠ x ∷ xs
  []≠∷ = false!
