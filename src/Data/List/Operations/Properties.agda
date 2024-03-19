{-# OPTIONS --safe #-}
module Data.List.Operations.Properties where

open import Foundations.Base
open import Correspondences.Decidable
open import Meta.Search.Discrete

open import Data.Bool.Base as Bool
open import Data.Bool.Properties
open import Data.Sum.Base as Sum
open import Data.Dec.Base as Dec
open import Data.List.Base as List
open import Data.List.Properties
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.Nat.Base

private variable
  ℓ ℓ′ : Level
  A : Type ℓ

++-snoc : (xs ys : List A) (y : A) → snoc xs y ++ ys ＝ xs ++ y ∷ ys
++-snoc []       ys y = refl
++-snoc (x ∷ xs) ys y = ap (x ∷_) (++-snoc xs ys y)

snoc-++ : (xs ys : List A) (y : A) → snoc (xs ++ ys) y ＝ xs ++ snoc ys y
snoc-++ []       ys y = refl
snoc-++ (x ∷ xs) ys y = ap (x ∷_) (snoc-++ xs ys y)

snoc-elim : (P : List A → 𝒰 ℓ′)
  → P []
  → (∀ xs x → P xs → P (snoc xs x))
  → ∀ xs → P xs
snoc-elim P p[] ps xs = go [] xs p[]
  where
  go : ∀ xs ys → P xs → P (xs ++ ys)
  go xs []       pxs = subst P (sym $ ++-id-r xs) pxs
  go xs (y ∷ ys) pxs = subst P (++-snoc xs ys y) (go (snoc xs y) ys (ps xs y pxs))

++-length : (xs ys : List A) → length (xs ++ ys) ＝ length xs + length ys
++-length []       ys = refl
++-length (x ∷ xs) ys = ap suc (++-length xs ys)

-- all

reflects-all : ∀ (p : A → Bool) xs
             → Reflects⁰ (All (⟦_⟧ᵇ ∘ p) xs) (all p xs)
reflects-all p []       = ofʸ []
reflects-all p (x ∷ xs) with p x | recall p x
... | false | ⟪ e ⟫ = ofⁿ (λ where (a ∷ as) → subst ⟦_⟧ᵇ e a)
... | true  | ⟪ e ⟫ = Reflects′.dmap (λ a → (subst ⟦_⟧ᵇ (sym e) tt) ∷ a)
                       (λ ne → λ where (px ∷ a) → ne a)
                       (reflects-all p xs)

-- elem

elem= : ⦃ A-dis : is-discrete A ⦄
      → A → List A → Bool
elem= = elem (λ a b → ⌊ a ≟ b ⌋)

all-elem : ⦃ A-dis : is-discrete A ⦄
         → ∀ (P : A → 𝒰 ℓ′) xs
         → All P xs
         → (z : A) → ⟦ elem= z xs ⟧ᵇ → P z
all-elem P (x ∷ xs) (px ∷ a) z el with (true-reflects (reflects-or {x = ⌊ z ≟ x ⌋}) el)
... | inl z=x = subst P (sym (true-reflects discrete-reflects z=x)) px
... | inr els = all-elem P xs a z els

elem-all : ⦃ A-dis : is-discrete A ⦄
         → ∀ (P : A → 𝒰 ℓ′) xs
         → ((z : A) → ⟦ elem= z xs ⟧ᵇ → P z)
         → All P xs
elem-all P []       f = []
elem-all P (x ∷ xs) f = (f x (reflects-true (reflects-or {x = ⌊ x ≟ x ⌋}) (inl (reflects-true discrete-reflects refl))))
                      ∷ (elem-all P xs (λ z el → f z (reflects-true (reflects-or {x = ⌊ z ≟ x ⌋}) (inr el))))

reflects-all-dis : ⦃ A-dis : is-discrete A ⦄
                 → ∀ (p : A → Bool) xs
                 → Reflects⁰ (∀ x → ⟦ elem= x xs ⟧ᵇ → ⟦ p x ⟧ᵇ) (all p xs)
reflects-all-dis p xs =
  Reflects′.dmap
    (all-elem (⟦_⟧ᵇ ∘ p) xs)
    (λ na e → na (elem-all (⟦_⟧ᵇ ∘ p) xs e))
    (reflects-all p xs)

-- replicate

All-replicate : {z : A} (xs : List A)
              → All (_＝ z) xs
              → xs ＝ replicate (length xs) z
All-replicate     []       []       = refl
All-replicate {z} (x ∷ xs) (xa ∷ a) = ap² List._∷_ xa (All-replicate xs a)

-- span

span-append : ∀ (p : A → Bool) xs
            → let (ys , zs) = span p xs in
              xs ＝ ys ++ zs
span-append p []       = refl
span-append p (x ∷ xs) with p x
... | true  = ap (x ∷_) (span-append p xs)
... | false = refl

span-length : ∀ (p : A → Bool) xs
            → let (ys , zs) = span p xs in
              length xs ＝ length ys + length zs
span-length p xs =
  let (ys , zs) = span p xs in
  ap length (span-append p xs) ∙ ++-length ys zs

span-all : ∀ (p : A → Bool) xs
         → All (⟦_⟧ᵇ ∘ p) (span p xs .fst)
span-all p []       = []
span-all p (x ∷ xs) with p x | recall p x
... | false | ⟪ e ⟫ = []
... | true  | ⟪ e ⟫ = subst ⟦_⟧ᵇ (sym e) tt ∷ (span-all p xs)
