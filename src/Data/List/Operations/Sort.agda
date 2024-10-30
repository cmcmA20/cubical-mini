{-# OPTIONS --safe #-}
module Data.List.Operations.Sort where

open import Meta.Prelude
open import Foundations.Base

open import Logic.Decidability
open import Logic.Discreteness

open import Order.Constructions.Minmax
open import Order.Constructions.Nat

open import Data.Empty as Empty
open import Data.Bool.Base as Bool
open import Data.Bool.Path
open import Data.Bool.Properties
open import Data.Sum.Base as Sum
open import Data.Dec.Base as Dec
open import Data.Reflects.Base as Reflects
open import Data.List.Base as List
open import Data.List.Path
open import Data.List.Properties
open import Data.List.Operations
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.At
open import Data.List.Correspondences.Unary.Related
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.Perm
open import Data.List.Correspondences.Binary.OPE
open import Data.Nat.Base
open import Data.Nat.Path
open import Data.Nat.Two
open import Data.Nat.Two.Properties
open import Data.Nat.Order.Base
open import Data.Nat.Properties

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″
  m n : ℕ
  xs : List A
  x y z w : A

insert-perm : (cmp : A → A → Bool) (x : A) (xs : List A)
            → Perm (insert cmp x xs) (x ∷ xs)
insert-perm cmp x []       = perm-refl
insert-perm cmp x (y ∷ xs) with cmp x y
... | false = ptrans (pprep refl (insert-perm cmp x xs)) (pswap refl refl perm-refl)
... | true  = perm-refl

insertion-sort-perm : (cmp : A → A → Bool) (xs : List A)
                    → Perm (insertion-sort cmp xs) xs
insertion-sort-perm cmp [] = perm-refl
insertion-sort-perm cmp (x ∷ xs) = ptrans (insert-perm cmp x (insertion-sort cmp xs)) (pprep refl (insertion-sort-perm cmp xs))

insert-sorted : (cmp : A → A → Bool) (x : A) (xs : List A)
              → Trans (λ x y → So (cmp x y))
              → (∀ x y → ¬ So (cmp x y) → So (cmp y x))
              → Sorted (λ x y → So (cmp x y)) xs
              → Sorted (λ x y → So (cmp x y)) (insert cmp x xs)
insert-sorted cmp x  []      tr tot []ˢ    = ∷ˢ []ʳ
insert-sorted cmp x (y ∷ xs) tr tot (∷ˢ r) with cmp x y | recall (cmp x) y
... | false | ⟪ eq ⟫ = ∷ˢ (sorted-at0→related
                              (insert-sorted cmp x xs tr tot (related→sorted r))
                              (all→atweak (perm-all (perm-sym (insert-perm cmp x xs))
                                                    (tot x y (¬so≃is-false ⁻¹ $ eq) ∷ (related→all ⦃ tr ⦄ r)))
                                          0))
... | true  | ⟪ eq ⟫ = ∷ˢ ((so≃is-true ⁻¹ $ eq) ∷ʳ r)

insertion-sort-sorted : (cmp : A → A → Bool) (xs : List A)
                      → Trans (λ x y → So (cmp x y))
                      → (∀ x y → ¬ So (cmp x y) → So (cmp y x))
                      → Sorted (λ x y → So (cmp x y)) (insertion-sort cmp xs)
insertion-sort-sorted cmp []       tr tot = []ˢ
insertion-sort-sorted cmp (x ∷ xs) tr tot =
  insert-sorted cmp x (insertion-sort cmp xs)
    tr tot
    (insertion-sort-sorted cmp xs tr tot)

-- sorting with strict comparison

insert-sorted-uniq-strict : (cmp : A → A → Bool) (x : A) (xs : List A)
                          → Trans (λ x y → So (cmp x y))
                          → (∀ x y → ¬ So (cmp x y) → So (cmp y x) ⊎ (x ＝ y))
                          → x ∉ xs
                          → Uniq xs
                          → Sorted (λ x y → So (cmp x y)) xs
                          → Sorted (λ x y → So (cmp x y)) (insert cmp x xs)
insert-sorted-uniq-strict cmp x  []      tr stot nx  u         []ˢ   = ∷ˢ []ʳ
insert-sorted-uniq-strict cmp x (y ∷ xs) tr stot nx (ny ∷ᵘ u) (∷ˢ r) with cmp x y | recall (cmp x) y
... | false | ⟪ eq ⟫ =
  let (ne , nxs) = ¬Any-uncons nx in
  ∷ˢ (sorted-at0→related
        (insert-sorted-uniq-strict cmp x xs tr stot nxs u (related→sorted r))
        (all→atweak (perm-all (perm-sym (insert-perm cmp x xs))
                              ([ id , (λ e → absurd (ne e)) ]ᵤ (stot x y (¬so≃is-false ⁻¹ $ eq)) ∷ (related→all ⦃ tr ⦄ r)))
                    0))
... | true  | ⟪ eq ⟫ = ∷ˢ ((so≃is-true ⁻¹ $ eq) ∷ʳ r)

insertion-sort-sorted-uniq-strict : (cmp : A → A → Bool) (xs : List A)
                                  → Trans (λ x y → So (cmp x y))
                                  → (∀ x y → ¬ So (cmp x y) → So (cmp y x) ⊎ (x ＝ y))
                                  → Uniq xs
                                  → Sorted (λ x y → So (cmp x y)) (insertion-sort cmp xs)
insertion-sort-sorted-uniq-strict cmp []       tr stot []ᵘ       = []ˢ
insertion-sort-sorted-uniq-strict cmp (x ∷ xs) tr stot (nx ∷ᵘ u) =
  let p = insertion-sort-perm cmp xs in
  insert-sorted-uniq-strict cmp x (insertion-sort cmp xs)
    tr stot
    (contra (≈↔→≈ {S = insertion-sort cmp xs} {T = xs} (perm→bag-equiv p) .fst) nx)
    (perm-unique (perm-sym p) u)
    (insertion-sort-sorted-uniq-strict cmp xs tr stot u)
