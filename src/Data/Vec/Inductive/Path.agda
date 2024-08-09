{-# OPTIONS --safe --no-exact-split #-}
module Data.Vec.Inductive.Path where

open import Meta.Prelude
open import Meta.Extensionality

open import Logic.Discreteness

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Empty.Base
open import Data.Vec.Inductive.Base as Vec
open import Data.Reflects.Base as Reflects
open import Data.Unit.Base

private variable
  ℓ ℓ′ ℓᵃ : Level
  @0 n : ℕ
  A : Type ℓᵃ
  x y : A
  xs ys : Vec A n
  b₁ b₂ : Bool

∷-head-inj : x ∷ xs ＝ y ∷ ys → x ＝ y
∷-head-inj = ap head

∷-tail-inj : x ∷ xs ＝ y ∷ ys → xs ＝ ys
∷-tail-inj = ap tail

module _ ⦃ sa : Extensional A ℓ ⦄ where
  Code-Vec : Vec A n → Vec A n → 𝒰 ℓ
  Code-Vec []       []       = ⊤
  Code-Vec (x ∷ xs) (y ∷ ys) = sa .Pathᵉ x y × Code-Vec xs ys

  code-vec-refl : (xs : Vec A n) → Code-Vec xs xs
  code-vec-refl []       = _
  code-vec-refl (x ∷ xs) = sa .reflᵉ x , code-vec-refl xs

  decode-vec : Code-Vec xs ys → xs ＝ ys
  decode-vec {xs = []}     {([])}   _       = refl
  decode-vec {xs = x ∷ xs} {y ∷ ys} (p , c) = ap² _∷_ (sa .idsᵉ .to-path p) (decode-vec c)

  code-vec-reflᴾ
    : {xs ys : Vec A n} (c : Code-Vec xs ys)
    → code-vec-refl xs ＝[ ap (Code-Vec xs) (decode-vec c) ]＝ c
  code-vec-reflᴾ {xs = []}     {([])}   _       = refl
  code-vec-reflᴾ {xs = x ∷ xs} {y ∷ ys} (p , c) = sa .idsᵉ .to-path-over p ,ₚ code-vec-reflᴾ c

  instance
    Extensional-Vec : Extensional (Vec A n) ℓ
    Extensional-Vec .Pathᵉ = Code-Vec
    Extensional-Vec .reflᵉ = code-vec-refl
    Extensional-Vec .idsᵉ .to-path = decode-vec
    Extensional-Vec .idsᵉ .to-path-over = code-vec-reflᴾ

opaque
  code-vec-is-of-hlevel
    : {k : HLevel} {xs ys : Vec A n} → is-of-hlevel (2 + k) A → is-of-hlevel (1 + k) (Code-Vec xs ys)
  code-vec-is-of-hlevel {xs = []}     {([])}   _  = hlevel _
  code-vec-is-of-hlevel {xs = x ∷ xs} {y ∷ ys} hl =
    ×-is-of-hlevel _ (hl x y) (code-vec-is-of-hlevel {xs = xs} hl)

  vec-is-of-hlevel : (k : HLevel)
                    → is-of-hlevel (2 + k) A
                    → is-of-hlevel (2 + k) (Vec A n)
  vec-is-of-hlevel n A-hl xs _ =
    ≃→is-of-hlevel (1 + n)
                   (identity-system-gives-path (Extensional-Vec .idsᵉ) ⁻¹)
                   (code-vec-is-of-hlevel {xs = xs} A-hl)

instance opaque
  H-Level-Vec : ∀ {k} → ⦃ k ≥ʰ 2 ⦄ → ⦃ A-hl : H-Level k A ⦄ → H-Level k (Vec A n)
  H-Level-Vec {k} ⦃ s≤ʰs (s≤ʰs _) ⦄ .H-Level.has-of-hlevel = vec-is-of-hlevel _ (hlevel k)
  {-# OVERLAPPING H-Level-Vec #-}

instance
  Reflects-∷=∷ : ⦃ rh : Reflects (x ＝ y) b₁ ⦄ ⦃ rt : Reflects (xs ＝ ys) b₂ ⦄ → Reflects (x ∷ xs ＝ y ∷ ys) (b₁ and b₂)
  Reflects-∷=∷ = Reflects.dmap (λ p → ap² _∷_ (p .fst) (p .snd)) (contra < ∷-head-inj , ∷-tail-inj >) auto

  Vec-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (Vec A n)
  Vec-is-discrete {x = []}     {([])}   = true because auto
  Vec-is-discrete {x = x ∷ xs} {y ∷ ys} .does  = (x =? y) and ⌊ Vec-is-discrete {x = xs} {y = ys} ⌋
  Vec-is-discrete {x = x ∷ xs} {y ∷ ys} .proof = Reflects-∷=∷ ⦃ auto ⦄ ⦃ Vec-is-discrete {x = xs} {y = ys} .proof ⦄
