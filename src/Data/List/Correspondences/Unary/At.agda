{-# OPTIONS --safe #-}
module Data.List.Correspondences.Unary.At where

open import Meta.Prelude
open import Meta.Extensionality
open Variadics _

open import Data.Empty.Base as ⊥
open import Data.List.Base
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.Nat.Base
open import Data.Nat.Order.Base
open import Data.Reflects as Reflects
open import Data.Sum.Base as Sum

private variable
  ℓᵃ ℓ : Level
  A : 𝒰 ℓᵃ
  P Q R : Pred A ℓ
  x : A
  @0 xs ys : List A

data At {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (P : Pred A ℓ) : @0 List A → @0 ℕ → 𝒰 (ℓᵃ ⊔ ℓ) where
  ahere  : ∀ {x} {@0 xs : List A} → (px : P x) → At P (x ∷ xs) zero
  athere : ∀ {n x} {@0 xs : List A} → (pxs : At P xs n) → At P (x ∷ xs) (suc n)

module _ {A : 𝒰 ℓᵃ} {P : Pred A ℓ} ⦃ ep : {a : A} → Extensional (P a) ℓ ⦄ where
  Code-At : {xs : List A} {n : ℕ} (p q : At P xs n) → 𝒰 ℓ
  Code-At {xs = x ∷ xs} (ahere px) (ahere qx) = ep .Pathᵉ px qx
  Code-At {xs = x ∷ xs} (athere p) (athere q) = Code-At p q

  code-at-refl : {xs : List A} {n : ℕ} (p : At P xs n) → Code-At p p
  code-at-refl {xs = x ∷ xs} (ahere px) = ep .reflᵉ px
  code-at-refl {xs = x ∷ xs} (athere p) = code-at-refl p

  decode-at : {xs : List A} {n : ℕ} {p q : At P xs n} (c : Code-At p q) → p ＝ q
  decode-at {xs = x ∷ xs} {p = ahere px} {q = ahere qx} c = ap ahere (ep .idsᵉ .to-path c)
  decode-at {xs = x ∷ xs} {p = athere p} {q = athere q} c = ap athere (decode-at c)

  decode-at-refl : {xs : List A} {n : ℕ} {p q : At P xs n} (c : Code-At p q)
                 → code-at-refl p ＝[ ap (Code-At p) (decode-at c) ]＝ c
  decode-at-refl {xs = x ∷ xs} {p = ahere px} {q = ahere qx} c =
    ep .idsᵉ .to-path-over c
  decode-at-refl {xs = x ∷ xs} {p = athere p} {q = athere q} c =
    decode-at-refl {xs = xs} c

  Extensional-At : {xs : List A} {n : ℕ} → Extensional (At P xs n) ℓ
  Extensional-At      .Pathᵉ              = Code-At
  Extensional-At      .reflᵉ              = code-at-refl
  Extensional-At      .idsᵉ .to-path      = decode-at
  Extensional-At {xs} .idsᵉ .to-path-over = decode-at-refl {xs = xs}

opaque
  code-at-is-of-hlevel
    : ∀ {k n} {xs : List A} {u v : At P xs n}
    → (∀ x → is-of-hlevel (suc k) (P x))
    → is-of-hlevel k (Code-At u v)
  code-at-is-of-hlevel {k = k} {(n)} {xs = x ∷ xs} {u = ahere ux} {v = ahere vx} hl =
    path-is-of-hlevel k (hl x) ux vx
  code-at-is-of-hlevel {k = k} {(n)} {xs = x ∷ xs} {u = athere u} {v = athere v} hl =
    code-at-is-of-hlevel {xs = xs} hl

at-contr-is-prop
    : {xs : List A} {n : ℕ}
    → (∀ x → is-contr (P x))
    → is-prop (At P xs n)
at-contr-is-prop {xs} {n} cp a b =
  ≃→is-of-hlevel 0
    (identity-system-gives-path (Extensional-At .idsᵉ) ⁻¹)
    (code-at-is-of-hlevel {k = 0} {u = a} {v = b} (is-of-hlevel-+ 0 1 ∘ cp))
    .fst

at-is-of-hlevel
  : (k : HLevel) {xs : List A} {n : ℕ}
  → (∀ x → is-of-hlevel (1 + k) (P x))
  → is-of-hlevel (1 + k) (At P xs n)
at-is-of-hlevel  zero   hl a1 a2 =
  ≃→is-of-hlevel 0
    (identity-system-gives-path (Extensional-At .idsᵉ) ⁻¹)
    (code-at-is-of-hlevel {u = a1} hl)
    .fst
at-is-of-hlevel (suc k) hl a1 a2 =
  ≃→is-of-hlevel (suc k)
    (identity-system-gives-path (Extensional-At .idsᵉ) ⁻¹)
    (code-at-is-of-hlevel {u = a1} hl)

instance opaque
  H-Level-At : ∀ {k} {xs : List A} {n : ℕ} → ⦃ k ≥ʰ 1 ⦄ → ⦃ A-hl : ∀ {x} → H-Level k (P x) ⦄ → H-Level k (At P xs n)
  H-Level-At {k} ⦃ s≤ʰs _ ⦄ .H-Level.has-of-hlevel = at-is-of-hlevel _ (λ _ → hlevel k)
  {-# OVERLAPPING H-Level-At #-}

¬at-[] : ∀ {n}
       → ¬ At P [] n
¬at-[] ()

¬at-oversize : ∀ {xs n}
             → length xs ≤ n
             → ¬ At P xs n
¬at-oversize {xs = x ∷ xs} le (ahere _)  = false! le
¬at-oversize {xs = x ∷ xs} le (athere a) = ¬at-oversize (≤-peel le) a

at-uncons : ∀ {x xs n}
          → At P (x ∷ xs) n
          → P x × (n ＝ 0) ⊎ At P xs (pred n)
at-uncons (ahere px) = inl (px , refl)
at-uncons (athere a) = inr a

at-map : ∀ {xs n} → ∀[ P ⇒ Q ] → At P xs n → At Q xs n
at-map {xs = x ∷ xs} f (ahere px)  = ahere (f px)
at-map {xs = x ∷ xs} f (athere at) = athere (at-map f at)

at-++-l : ∀ {xs ys n} → At P xs n → At P (xs ++ ys) n
at-++-l {xs = x ∷ xs} (ahere px)  = ahere px
at-++-l {xs = x ∷ xs} (athere at) = athere (at-++-l at)

at-++-r : ∀ {xs ys n} → At P ys n → At P (xs ++ ys) (length xs + n)
at-++-r {xs = []}     ay = ay
at-++-r {xs = x ∷ xs} ay = athere (at-++-r ay)

at-++-split : ∀ {xs ys n} → At P (xs ++ ys) n → At P xs n ⊎ (length xs ≤ n) × At P ys (n ∸ length xs)
at-++-split {xs = []}      a         = inr (z≤ , a)
at-++-split {xs = x ∷ xs} (ahere px) = inl (ahere px)
at-++-split {xs = x ∷ xs} (athere a) = Sum.dmap athere (first s≤s) (at-++-split a)

all→at : {xs : List A}
       → All P xs → ∀ n → n < length xs → At P xs n
all→at {xs = []}      a       n      nlt = false! nlt
all→at {xs = x ∷ xs} (px ∷ _) zero   nlt = ahere px
all→at {xs = x ∷ xs} (_ ∷ a) (suc n) nlt = athere (all→at a n (<-peel nlt))

any→at : {@0 xs : List A}
       → (a : Any P xs) → At P xs (any→ℕ a)
any→at (here px) = ahere px
any→at (there a) = athere (any→at a)

at∈ : ∀ {xs z} → (x∈ : z ∈ xs) → At P xs (any→ℕ x∈) → P z
at∈ {P} {xs = x ∷ xs} (here e)   (ahere px)  = subst P (e ⁻¹) px
at∈     {xs = x ∷ xs} (there x∈) (athere ax) = at∈ x∈ ax

-- the weak version, allowing the element to not be included

data AtWeak {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (P : Pred A ℓ) : @0 List A → @0 ℕ → 𝒰 (ℓᵃ ⊔ ℓ) where
  awnil  : ∀ {n} → AtWeak P [] n
  awhere  : ∀ {x xs} → (px : P x) → AtWeak P (x ∷ xs) zero
  awthere : ∀ {n x xs} → (pxs : AtWeak P xs n) → AtWeak P (x ∷ xs) (suc n)

atweak-map : ∀ {xs n} → ∀[ P ⇒ Q ] → AtWeak P xs n → AtWeak Q xs n
atweak-map {xs = []} f  awnil       = awnil
atweak-map           f (awhere px)  = awhere (f px)
atweak-map           f (awthere aw) = awthere (atweak-map f aw)

at→atweak : ∀ {xs n} → At P xs n → AtWeak P xs n
at→atweak {xs = x ∷ xs} (ahere px) = awhere px
at→atweak {xs = x ∷ xs} (athere a) = awthere (at→atweak a)

all→atweak : ∀ {xs} → All P xs → ∀ n → AtWeak P xs n
all→atweak {xs = []}     []        n      = awnil
all→atweak {xs = x ∷ xs} (px ∷ _)  zero   = awhere px
all→atweak {xs = x ∷ xs} (_ ∷ a)  (suc n) = awthere (all→atweak a n)

atweak∈ : ∀ {xs x} → (x∈ : x ∈ xs) → AtWeak P xs (any→ℕ x∈) → P x
atweak∈ {P} {xs = x ∷ xs} (here e)   (awhere px)  =
  subst P (e ⁻¹) px
atweak∈     {xs = x ∷ xs} (there x∈) (awthere aw) =
  atweak∈ x∈ aw
