{-# OPTIONS --safe --no-exact-split #-}
module Data.List.Correspondences.Unary.Any where

open import Meta.Prelude
open import Meta.Extensionality
open Variadics _

open import Data.Bool.Base
open import Data.Dec.Base as Dec
open import Data.Empty.Base as ⊥
open import Data.Fin.Computational.Base
open import Data.Fin.Computational.Path
open import Data.List.Base
open import Data.List.Instances.Map
open import Data.List.Operations
open import Data.Nat.Base
open import Data.Reflects.Base as Reflects
open import Data.Sum.Base

private variable
  ℓᵃ ℓᵇ ℓ ℓ′ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  P Q R : Pred A ℓ
  S : Pred B ℓ′
  x : A
  @0 xs ys : List A
  b : Bool

data Any {ℓᵃ ℓ} {A : 𝒰 ℓᵃ} (P : Pred A ℓ) : @0 List A → 𝒰 (ℓᵃ ⊔ ℓ) where
  here  : (px : P x) → Any P (x ∷ xs)
  there : (pxs : Any P xs) → Any P (x ∷ xs)

module _ {A : 𝒰 ℓᵃ} {P : Pred A ℓ} ⦃ ep : {a : A} → Extensional (P a) ℓ ⦄ where
  Code-Any : {xs : List A} (p q : Any P xs) → 𝒰 ℓ
  Code-Any {xs = x ∷ xs} (here px) (here qx) = ep .Pathᵉ px qx
  Code-Any {xs = x ∷ xs} (there p) (there q) = Code-Any p q
  Code-Any {xs = x ∷ xs} _         _         = ⊥

  code-any-refl : {xs : List A} (p : Any P xs) → Code-Any p p
  code-any-refl {xs = x ∷ xs} (here px) = ep .reflᵉ px
  code-any-refl {xs = x ∷ xs} (there p) = code-any-refl p

  encode-any : {xs : List A} {p q : Any P xs} → p ＝ q → Code-Any p q
  encode-any {p} e = subst (Code-Any p) e (code-any-refl p)

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
  -- TODO feels like it can be strengthened
  code-any-is-of-hlevel
    : ∀ {n} {xs : List A} {u v : Any P xs}
    → (∀ x → is-of-hlevel (2 + n) (P x))
    → is-of-hlevel (1 + n) (Code-Any u v)
  code-any-is-of-hlevel {n} {xs = x ∷ xs} {u = here ux} {v = here vx} hl = path-is-of-hlevel (suc n) (hl x) ux vx
  code-any-is-of-hlevel {n} {xs = x ∷ xs} {u = here ux} {v = there v} hl = hlevel (suc n)
  code-any-is-of-hlevel {n} {xs = x ∷ xs} {u = there u} {v = here vx} hl = hlevel (suc n)
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

is-here? is-there? : Any P xs → Bool
is-here? (here  _) = true
is-here? (there _) = false
is-there? = not ∘ is-here?

here-inj : {xs : List A} {p q : P x} → here {P = P} {xs = xs} p ＝ here q → p ＝ q
here-inj {x} {xs} = encode-any {xs = x ∷ xs}

there-inj : {xs : List A} {p q : Any P xs} → there {x = x} p ＝ there q → p ＝ q
there-inj {x} {xs} = decode-any ∘ encode-any {xs = x ∷ xs}

instance
  Reflects-here≠there
    : {p : P x} {q : Any P xs}
    → Reflects (here p ＝ there q) false
  Reflects-here≠there = ofⁿ (λ z → ¬-so-false (subst So (ap is-here? z) oh))

  Reflects-there≠here
    : {p : P x} {q : Any P xs}
    → Reflects (there q ＝ here p) false
  Reflects-there≠here = ofⁿ (λ z → ¬-so-false (subst So (ap is-there? z) oh))

  Reflects-here=here
    : {xs : List A} {p q : P x} ⦃ _ : Reflects (p ＝ q) b ⦄
    → Reflects (Path (Any P (x ∷ xs)) (here p) (here q)) b
  Reflects-here=here {xs} = Reflects.dmap (ap here) (contra here-inj) auto

  Reflects-there=there
    : {xs : List A} {p q : Any P xs} ⦃ _ : Reflects (p ＝ q) b ⦄
    → Reflects (Path (Any P (x ∷ xs)) (there p) (there q)) b
  Reflects-there=there {xs} = Reflects.dmap (ap there) (contra there-inj) auto

opaque
  here≠there : {p : P x} {q : Any P xs} → here p ≠ there q
  here≠there = false!

opaque
  there≠here : {p : P x} {q : Any P xs} → there q ≠ here p
  there≠here = false!

instance
  Reflects-any-tail : {xs : List A} → ⦃ Reflects (Any P xs) true ⦄ → Reflects (Any P (x ∷ xs)) true
  Reflects-any-tail = ofʸ (there true!)
  {-# OVERLAPPABLE Reflects-any-tail #-}

  ¬Any[] : Reflects (Any P []) false
  ¬Any[] = ofⁿ λ ()

¬Any-∷ : {x : A} {xs : List A}
       → ¬ P x → ¬ Any P xs → ¬ Any P (x ∷ xs)
¬Any-∷ nx nxs (here px)   = nx px
¬Any-∷ nx nxs (there pxs) = nxs pxs

¬Any-uncons : {x : A} {xs : List A}
            → ¬ Any P (x ∷ xs)
            → (¬ P x) × (¬ Any P xs)
¬Any-uncons na = contra here na , contra there na

any-++-l : {@0 xs ys : List A} → Any P xs → Any P (xs ++ ys)
any-++-l (here px)  = here px
any-++-l (there ax) = there (any-++-l ax)

any-++-r : {xs ys : List A} → Any P ys → Any P (xs ++ ys)
any-++-r {xs = []}     ay = ay
any-++-r {xs = x ∷ xs} ay = there (any-++-r ay)

any-uncons : {x : A} {xs : List A} → Any P (x ∷ xs) → P x ⊎ Any P xs
any-uncons (here px) = inl px
any-uncons (there a) = inr a

any-split : {xs ys : List A} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
any-split {xs = []}      a        = inr a
any-split {xs = _ ∷ _}  (here px) = inl (here px)
any-split {xs = _ ∷ xs} (there a) = [ inl ∘ there , inr ]ᵤ (any-split {xs = xs} a)

any-map : {@0 xs : List A} → ∀[ P ⇒ Q ] → Any P xs → Any Q xs
any-map f (here px) = here (f px)
any-map f (there a) = there (any-map f a)

any→map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {S : Pred B ℓ′} {f : A → B} {xs : List A}
        → Any (S ∘ f) xs → Any S (map f xs)
any→map {xs = x ∷ xs} (here sfx) = here sfx
any→map {xs = x ∷ xs} (there a)  = there (any→map a)

any←map : {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {S : Pred B ℓ′} {f : A → B} {xs : List A}
        → Any S (map f xs) → Any (S ∘ f) xs
any←map {xs = x ∷ xs} (here sfx) = here sfx
any←map {xs = x ∷ xs} (there a)  = there (any←map a)

any→ℕ : {@0 xs : List A} → Any P xs → ℕ
any→ℕ (here _)  = 0
any→ℕ (there a) = suc (any→ℕ a)

any→fin : {xs : List A} → Any P xs → Fin (length xs)
any→fin {xs = x ∷ xs} (here _)  = fzero
any→fin {xs = x ∷ xs} (there a) = fsuc (any→fin a)

any→fin-!ᶠ : {xs : List A} → (a : Any P xs) → P (xs !ᶠ any→fin a)
any→fin-!ᶠ {xs = x ∷ xs} (here px) = px
any→fin-!ᶠ {xs = x ∷ xs} (there a) = any→fin-!ᶠ a
