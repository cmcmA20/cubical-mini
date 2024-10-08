{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.Any where

open import Prelude

open import Data.List.Base
open import Data.List.Operations
open import Data.Empty.Base
open import Data.Sum.Base
open import Data.Nat.Base
open import Data.Fin.Base

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ
  P Q R : Pred A ℓ
  x : A
  @0 xs ys : List A

data Any {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (P : Pred A ℓ) : @0 List A → 𝒰 (ℓᵃ ⊔ ℓ) where
  here  : ∀ {x} {@0 xs : List A} → (px : P x) → Any P (x ∷ xs)
  there : ∀ {x} {@0 xs : List A} → (pxs : Any P xs) → Any P (x ∷ xs)

module _ {A : 𝒰 ℓᵃ} {P : Pred A ℓ} ⦃ ep : {a : A} → Extensional (P a) ℓ ⦄ where
  Code-Any : {xs : List A} (p q : Any P xs) → 𝒰 ℓ
  Code-Any {xs = x ∷ xs} (here px) (here qx) = ep .Pathᵉ px qx
  Code-Any {xs = x ∷ xs} (here px) (there q) = ⊥
  Code-Any {xs = x ∷ xs} (there p) (here qx) = ⊥
  Code-Any {xs = x ∷ xs} (there p) (there q) = Code-Any p q

  code-any-refl : {xs : List A} (p : Any P xs) → Code-Any p p
  code-any-refl {xs = x ∷ xs} (here px) = ep .reflᵉ px
  code-any-refl {xs = x ∷ xs} (there p) = code-any-refl p

  decode-any : {xs : List A} {p q : Any P xs} (c : Code-Any p q) → p ＝ q
  decode-any {xs = x ∷ xs} {here px} {here qx} c = ap here (ep .idsᵉ .to-path c)
  decode-any {xs = x ∷ xs} {there p} {there q} c = ap there (decode-any c)

  decode-any-refl : {xs : List A} {p q : Any P xs} (c : Code-Any p q)
                  → code-any-refl p ＝[ ap (Code-Any p) (decode-any c) ]＝ c
  decode-any-refl {xs = x ∷ xs} {here px} {here qx} c = ep .idsᵉ .to-path-over c
  decode-any-refl {xs = x ∷ xs} {there p} {there q} c = decode-any-refl {p = p} {q = q} c

  instance
    Extensional-Any : {xs : List A} → Extensional (Any P xs) ℓ
    Extensional-Any      .Pathᵉ              = Code-Any
    Extensional-Any      .reflᵉ              = code-any-refl
    Extensional-Any      .idsᵉ .to-path      = decode-any
    Extensional-Any {xs} .idsᵉ .to-path-over = decode-any-refl {xs}

opaque
  code-any-is-of-hlevel
    : ∀ {n} {xs : List A} {u v : Any P xs}
    → (∀ x → is-of-hlevel (2 + n) (P x))
    → is-of-hlevel (1 + n) (Code-Any u v)
  code-any-is-of-hlevel {n} {xs = x ∷ xs} {u = here ux} {v = here vx} hl = path-is-of-hlevel (suc n) (hl x) ux vx
  code-any-is-of-hlevel {n} {xs = x ∷ xs} {u = here ux} {v = there v} hl = hlevel!
  code-any-is-of-hlevel {n} {xs = x ∷ xs} {u = there u} {v = here vx} hl = hlevel!
  code-any-is-of-hlevel {n} {xs = x ∷ xs} {u = there u} {v = there v} hl = code-any-is-of-hlevel {u = u} {v = v} hl

-- technically it's also a set when P has level 0/1
any-is-of-hlevel
  : (n : HLevel) {xs : List A}
  → (∀ x → is-of-hlevel (2 + n) (P x))
  → is-of-hlevel (2 + n) (Any P xs)
any-is-of-hlevel n {xs} hl a1 a2 =
  ≃→is-of-hlevel (1 + n)
    (identity-system-gives-path (Extensional-Any .idsᵉ) ⁻¹)
    (code-any-is-of-hlevel {u = a1} hl)

instance opaque
  H-Level-Any : ∀ {n} {xs : List A} → ⦃ n ≥ʰ 2 ⦄ → ⦃ A-hl : ∀ {x} → H-Level n (P x) ⦄ → H-Level n (Any P xs)
  H-Level-Any {n} ⦃ s≤ʰs (s≤ʰs _) ⦄ .H-Level.has-of-hlevel = any-is-of-hlevel _ (λ _ → hlevel n)
  {-# OVERLAPPING H-Level-Any #-}

¬Any-[] : ¬ Any P []
¬Any-[] ()

¬Any-∷ : {x : A} {xs : List A}
       → ¬ P x → ¬ Any P xs → ¬ Any P (x ∷ xs)
¬Any-∷ nx nxs (here px)   = nx px
¬Any-∷ nx nxs (there pxs) = nxs pxs

any-++-l : {@0 xs ys : List A} → Any P xs → Any P (xs ++ ys)
any-++-l (here px)  = here px
any-++-l (there ax) = there (any-++-l ax)

any-++-r : {xs ys : List A} → Any P ys → Any P (xs ++ ys)
any-++-r {xs = []}     ay = ay
any-++-r {xs = x ∷ xs} ay = there (any-++-r ay)

any-split : {xs ys : List A} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
any-split {xs = []}      a        = inr a
any-split {xs = x ∷ xs} (here px) = inl (here px)
any-split {xs = x ∷ xs} (there a) = [ inl ∘ there , inr ]ᵤ (any-split {xs = xs} a)

any-map : {@0 xs : List A} → ∀[ P ⇒ Q ] → Any P xs → Any Q xs
any-map f (here px) = here (f px)
any-map f (there a) = there (any-map f a)

any→ℕ : {@0 xs : List A} → Any P xs → ℕ
any→ℕ (here px) = 0
any→ℕ (there a) = suc (any→ℕ a)

any→fin : {xs : List A} → Any P xs → Fin (length xs)
any→fin {xs = x ∷ xs} (here px) = fzero
any→fin {xs = x ∷ xs} (there a) = fsuc (any→fin a)
